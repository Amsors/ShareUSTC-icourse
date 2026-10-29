#!/usr/bin/env python3
"""icourse.club 全站只读抓取器。

抓取范围：
* 全部课程（/course/ 列表发现）；
* 每门课程的全部可见点评（课程页一次性返回）；
* 每条点评的全部可见评论（点评 HTML 内嵌，不额外请求评论接口）。

不抓取：站点统计、教师主页、头像、专业培养方案等与评课数据无关的内容。

存储布局：
    data/
      manifest.json
      course_ids.json
      courses/<course_id>.json
      reviews/<course_id>/<review_id>.json
      _errors/<时间>_course-<id>[_review-<id>][_comment-<n>].json/.html

只读：仅 GET 课程/列表页面 + POST 登录，不调用点赞、发评、删评等写接口。
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
import threading
import time
import traceback
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

import requests

from icourse_client import (
    BASE_URL,
    ICourseClient,
    ICourseError,
    PAGE_SIZE,
    parse_course_list,
    parse_course_page,
)

VERSION = 1
REVIEW_ID_RE = re.compile(r"点评\s*(\d+)")


# --------------------------------------------------------------------------- #
# 异常
# --------------------------------------------------------------------------- #


class CrawlAborted(RuntimeError):
    """其他线程已触发停止。"""


class FetchError(RuntimeError):
    def __init__(
        self,
        message: str,
        *,
        path: str | None = None,
        status: int | None = None,
        body: str = "",
    ) -> None:
        super().__init__(message)
        self.path = path
        self.status = status
        self.body = body
        self.dump_path: Path | None = None


class SchemaMismatch(RuntimeError):
    """实际 HTML 与解析器预期不符，已主动停止。"""

    def __init__(
        self,
        message: str,
        *,
        course_id: str | None = None,
        context: dict[str, Any] | None = None,
        dump_path: Path | None = None,
    ) -> None:
        super().__init__(message)
        self.course_id = course_id
        self.context = context or {}
        self.dump_path = dump_path


# --------------------------------------------------------------------------- #
# 配置 / 工具
# --------------------------------------------------------------------------- #


@dataclass
class Config:
    data_dir: Path
    username: str
    password: str
    workers: int = 8
    rps: float = 2.0
    burst: int = 0
    timeout: float = 30.0
    retries: int = 3
    backoff: float = 1.0
    refresh: float = 1.0
    limit_pages: int = 0
    limit_courses: int = 0
    course_ids: list[str] = field(default_factory=list)
    resume: bool = False
    quiet: bool = False

    @property
    def courses_dir(self) -> Path:
        return self.data_dir / "courses"

    @property
    def reviews_dir(self) -> Path:
        return self.data_dir / "reviews"

    @property
    def errors_dir(self) -> Path:
        return self.data_dir / "_errors"

    @property
    def ids_path(self) -> Path:
        return self.data_dir / "course_ids.json"

    @property
    def manifest_path(self) -> Path:
        return self.data_dir / "manifest.json"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def human_bytes(value: float) -> str:
    units = ["B", "KiB", "MiB", "GiB", "TiB"]
    number = float(value)
    for unit in units:
        if abs(number) < 1024 or unit == units[-1]:
            return f"{number:.1f} {unit}" if unit != "B" else f"{int(number)} B"
        number /= 1024
    return f"{number:.1f} TiB"


def fmt_duration(seconds: float) -> str:
    seconds = max(0, int(seconds))
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    return f"{hours:02d}:{minutes:02d}:{secs:02d}"


def atomic_write_text(path: Path, text: str, stats: "Stats") -> bool:
    """原子写文件；返回是否新建。"""
    path.parent.mkdir(parents=True, exist_ok=True)
    old_size = path.stat().st_size if path.exists() else None
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)
    new_size = path.stat().st_size
    stats.note_file(old_size, new_size)
    return old_size is None


def atomic_write_json(path: Path, value: Any, stats: "Stats") -> bool:
    text = json.dumps(value, ensure_ascii=False, indent=2)
    return atomic_write_text(path, text, stats)


# --------------------------------------------------------------------------- #
# 统计 / 实时面板
# --------------------------------------------------------------------------- #


class Stats:
    def __init__(self, data_dir: Path) -> None:
        self.lock = threading.Lock()
        self.start = time.monotonic()
        self.last_time = self.start
        self.requests = 0
        self.bytes = 0
        self.files = 0
        self.file_bytes = 0
        self.courses_done = 0
        self.total_courses: int | None = None
        self.reviews = 0
        self.comments = 0
        self.skipped = 0
        self.errors = 0
        self.active = 0
        self._scan_existing(data_dir)
        with self.lock:
            self.last_requests = self.requests
            self.last_bytes = self.bytes

    def _scan_existing(self, data_dir: Path) -> None:
        if not data_dir.exists():
            return
        for root, _dirs, files in os.walk(data_dir):
            for name in files:
                if name.endswith(".tmp"):
                    continue
                path = Path(root) / name
                try:
                    size = path.stat().st_size
                except OSError:
                    continue
                self.files += 1
                self.file_bytes += size

    # -- 计数器 ---------------------------------------------------------- #

    def note_request(self) -> None:
        with self.lock:
            self.requests += 1

    def note_bytes(self, count: int) -> None:
        with self.lock:
            self.bytes += count

    def note_file(self, old_size: int | None, new_size: int) -> None:
        with self.lock:
            if old_size is None:
                self.files += 1
            self.file_bytes += new_size - (old_size or 0)

    def begin_task(self) -> None:
        with self.lock:
            self.active += 1

    def end_task(self) -> None:
        with self.lock:
            self.active -= 1

    def note_course(self, review_count: int, comment_count: int) -> None:
        with self.lock:
            self.courses_done += 1
            self.reviews += review_count
            self.comments += comment_count

    def note_skipped(self) -> None:
        with self.lock:
            self.courses_done += 1
            self.skipped += 1

    def note_error(self) -> None:
        with self.lock:
            self.errors += 1

    def set_total_courses(self, total: int) -> None:
        with self.lock:
            self.total_courses = total

    # -- 快照 ------------------------------------------------------------ #

    def snapshot(self) -> dict[str, Any]:
        with self.lock:
            now = time.monotonic()
            delta = now - self.last_time
            req_rate = (self.requests - self.last_requests) / delta if delta > 0 else 0.0
            bandwidth = (self.bytes - self.last_bytes) / delta if delta > 0 else 0.0
            self.last_time = now
            self.last_requests = self.requests
            self.last_bytes = self.bytes
            return {
                "elapsed": now - self.start,
                "requests": self.requests,
                "bytes": self.bytes,
                "request_rate": req_rate,
                "bandwidth": bandwidth,
                "files": self.files,
                "file_bytes": self.file_bytes,
                "courses_done": self.courses_done,
                "total_courses": self.total_courses,
                "reviews": self.reviews,
                "comments": self.comments,
                "skipped": self.skipped,
                "errors": self.errors,
                "active": self.active,
            }

    def summary(self) -> dict[str, Any]:
        with self.lock:
            elapsed = max(time.monotonic() - self.start, 1e-9)
            return {
                "elapsed_seconds": elapsed,
                "requests": self.requests,
                "bytes": self.bytes,
                "request_rate": self.requests / elapsed,
                "bandwidth": self.bytes / elapsed,
                "files": self.files,
                "file_bytes": self.file_bytes,
                "courses_done": self.courses_done,
                "total_courses": self.total_courses,
                "reviews": self.reviews,
                "comments": self.comments,
                "skipped": self.skipped,
                "errors": self.errors,
            }


class Reporter(threading.Thread):
    def __init__(self, stats: Stats, refresh: float, quiet: bool) -> None:
        super().__init__(daemon=True, name="stats-reporter")
        self.stats = stats
        self.refresh = refresh
        self.quiet = quiet
        self.tty = sys.stdout.isatty()
        self._stop = threading.Event()
        self._running = False

    def run(self) -> None:
        while not self._stop.wait(self.refresh):
            if self.quiet:
                continue
            try:
                self._emit(self.stats.snapshot())
            except Exception:  # 面板不能影响抓取
                pass

    def _emit(self, snap: dict[str, Any]) -> None:
        total = snap["total_courses"]
        progress = f"{snap['courses_done']}/{total}" if total is not None else f"{snap['courses_done']}/?"
        line = (
            f"[{fmt_duration(snap['elapsed'])}] "
            f"req={snap['requests']:,} ({snap['request_rate']:.1f}/s) "
            f"bytes={human_bytes(snap['bytes'])} ({human_bytes(snap['bandwidth'])}/s) | "
            f"courses={progress} reviews={snap['reviews']:,} comments={snap['comments']:,} | "
            f"files={snap['files']:,} ({human_bytes(snap['file_bytes'])}) | "
            f"active={snap['active']} skip={snap['skipped']:,} err={snap['errors']}"
        )
        if self.tty:
            sys.stdout.write("\r\x1b[2K" + line)
            sys.stdout.flush()
        else:
            print(line, flush=True)

    def start(self) -> None:
        self._running = True
        super().start()

    def stop(self) -> None:
        self._stop.set()
        if self._running:
            self.join(timeout=3)
        if self.tty and self._running:
            sys.stdout.write("\n")
            sys.stdout.flush()


# --------------------------------------------------------------------------- #
# 限流 / HTTP
# --------------------------------------------------------------------------- #


class RateLimiter:
    def __init__(self, rps: float, burst: int) -> None:
        self.enabled = rps > 0
        self.rate = rps
        self.capacity = max(1, burst if burst > 0 else int(max(1, rps)))
        self.tokens = float(self.capacity)
        self.updated = time.monotonic()
        self.lock = threading.Lock()

    def acquire(self, stop: threading.Event) -> bool:
        if not self.enabled:
            return not stop.is_set()
        while not stop.is_set():
            with self.lock:
                now = time.monotonic()
                self.tokens = min(
                    self.capacity,
                    self.tokens + (now - self.updated) * self.rate,
                )
                self.updated = now
                if self.tokens >= 1.0:
                    self.tokens -= 1.0
                    return True
                wait = (1.0 - self.tokens) / self.rate
            if stop.wait(wait):
                return False
        return False


class SessionPool:
    """每个线程一个 requests.Session，避免共享 cookie jar 的并发问题。"""

    def __init__(self, base: requests.Session) -> None:
        self.headers = dict(base.headers)
        self.cookies = base.cookies.copy()
        self.local = threading.local()

    def get(
        self, url: str, params: dict[str, Any] | None, timeout: float
    ) -> requests.Response:
        session = getattr(self.local, "session", None)
        if session is None:
            session = requests.Session()
            session.headers.update(self.headers)
            session.cookies.update(self.cookies)
            self.local.session = session
        return session.get(url, params=params, timeout=timeout, allow_redirects=True)


def fetch_html(
    pool: SessionPool,
    limiter: RateLimiter,
    stats: Stats,
    stop: threading.Event,
    cfg: Config,
    path: str,
    params: dict[str, Any] | None = None,
) -> tuple[str, requests.Response]:
    last_error: Exception | None = None
    for attempt in range(cfg.retries + 1):
        if stop.is_set():
            raise CrawlAborted("停止标志已设置")
        if not limiter.acquire(stop):
            raise CrawlAborted("限流等待时收到停止信号")
        stats.note_request()
        try:
            response = pool.get(BASE_URL + path, params, cfg.timeout)
            body = response.content
            stats.note_bytes(len(body))
            text = response.text
            if response.status_code != 200:
                raise FetchError(
                    f"HTTP {response.status_code} {path}",
                    path=path,
                    status=response.status_code,
                    body=text,
                )
            content_type = response.headers.get("content-type", "").lower()
            if "text/html" not in content_type:
                raise FetchError(
                    f"非 HTML 响应：{content_type} {path}",
                    path=path,
                    status=response.status_code,
                    body=text,
                )
            if "/signin" in response.url:
                raise FetchError(
                    f"被重定向到登录页：{response.url}",
                    path=path,
                    status=response.status_code,
                    body=text,
                )
            return text, response
        except (requests.RequestException, FetchError) as exc:
            last_error = exc
            if attempt >= cfg.retries:
                break
            delay = cfg.backoff * (2**attempt) + random.uniform(0, 0.3)
            if stop.wait(delay):
                raise CrawlAborted("重试等待时收到停止信号") from exc
    if isinstance(last_error, FetchError):
        raise last_error
    raise FetchError(
        f"请求失败：{path}: {last_error}",
        path=path,
    ) from last_error


# --------------------------------------------------------------------------- #
# 错误现场
# --------------------------------------------------------------------------- #


def _html_excerpt(html: str, review_id: str | None, limit: int = 50000) -> str:
    if review_id:
        match = re.search(rf'id="review-{re.escape(review_id)}"', html)
        if match:
            start = max(0, match.start() - limit // 2)
            end = min(len(html), match.end() + limit // 2)
            return html[start:end]
    if len(html) <= limit:
        return html
    return html[: limit - 2000] + "\n...\n" + html[-2000:]


def _partial_course(html: str, course_id: str) -> dict[str, Any] | None:
    try:
        data = parse_course_page(html, course_id=course_id, strict=False)
    except Exception:
        return None
    reviews = data.pop("reviews", [])
    summary = [
        {
            key: review.get(key)
            for key in (
                "review_id",
                "author",
                "author_id",
                "anonymous",
                "rating",
                "term",
                "created_at",
                "upvotes",
                "comment_count",
            )
        }
        for review in reviews
    ]
    data["reviews"] = summary
    return data


def _find_partial_review(
    html: str, course_id: str, review_id: str | None
) -> dict[str, Any] | None:
    if not review_id:
        return None
    try:
        data = parse_course_page(html, course_id=course_id, strict=False)
    except Exception:
        return None
    for review in data.get("reviews", []):
        if review.get("review_id") == review_id:
            return review
    return None


def save_error(
    cfg: Config,
    stats: Stats,
    *,
    message: str,
    course_id: str | None,
    context: dict[str, Any] | None = None,
    html: str | None = None,
    partial_course: dict[str, Any] | None = None,
    partial_review: dict[str, Any] | None = None,
    kind: str = "schema_mismatch",
) -> Path:
    context = context or {}
    review_id = str(context["review_id"]) if context.get("review_id") else None
    comment_index = context.get("comment_index")
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    stem = f"{timestamp}_course-{course_id or 'unknown'}"
    if review_id:
        stem += f"_review-{review_id}"
    if comment_index:
        stem += f"_comment-{comment_index}"
    cfg.errors_dir.mkdir(parents=True, exist_ok=True)

    html_path: Path | None = None
    if html is not None:
        html_path = cfg.errors_dir / f"{stem}.html"
        atomic_write_text(html_path, html, stats)

    payload = {
        "version": VERSION,
        "kind": kind,
        "time": now_iso(),
        "message": message,
        "course_id": course_id,
        "course_url": f"{BASE_URL}/course/{course_id}/" if course_id else None,
        "review_id": review_id,
        "comment_index": comment_index,
        "context": context,
        "html_path": str(html_path) if html_path else None,
        "html_excerpt": _html_excerpt(html, review_id) if html else None,
        "partial_course": partial_course,
        "partial_review": partial_review,
        "stats": stats.summary(),
    }
    json_path = cfg.errors_dir / f"{stem}.json"
    atomic_write_json(json_path, payload, stats)
    return json_path


# --------------------------------------------------------------------------- #
# 课程发现
# --------------------------------------------------------------------------- #


def _validate_list_page(
    page: int,
    total: int,
    pages: int,
    items: list[dict[str, Any]],
) -> None:
    expected = min(PAGE_SIZE, max(0, total - (page - 1) * PAGE_SIZE))
    if len(items) != expected:
        raise ICourseError(
            f"列表第 {page} 页预期 {expected} 门课，实际 {len(items)} 门",
            context={"page": page, "total": total, "pages": pages},
        )
    for item in items:
        cid = item.get("course_id")
        if not cid or not str(cid).isdigit():
            raise ICourseError(
                f"列表第 {page} 页存在非法课程 ID：{cid!r}",
                context={"page": page},
            )
        if not item.get("title"):
            raise ICourseError(
                f"列表第 {page} 页课程 {cid} 缺少标题",
                context={"page": page, "course_id": cid},
            )


def discover_courses(
    cfg: Config,
    pool: SessionPool,
    limiter: RateLimiter,
    stats: Stats,
    stop: threading.Event,
) -> tuple[list[str], dict[str, Any]]:
    if cfg.course_ids:
        return cfg.course_ids, {
            "source": "cli",
            "total": len(cfg.course_ids),
            "pages": None,
            "fetched_pages": None,
            "complete": True,
            "limited": False,
        }

    if cfg.resume and not cfg.limit_pages and cfg.ids_path.exists():
        try:
            cached = json.loads(cfg.ids_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            cached = None
        if cached and cached.get("complete") and cached.get("ids"):
            ids = [str(value) for value in cached["ids"]]
            return ids, {
                "source": "resume",
                "total": int(cached.get("total") or len(ids)),
                "pages": cached.get("pages"),
                "fetched_pages": cached.get("fetched_pages"),
                "complete": True,
                "limited": bool(cached.get("limited")),
            }

    html, _resp = fetch_html(pool, limiter, stats, stop, cfg, "/course/", {"page": 1})
    first = parse_course_list(html)
    total = first.get("total")
    pages = first.get("pages")
    if not total or not pages:
        raise SchemaMismatch(
            "课程列表第 1 页缺少总数/页数",
            context={"page": 1},
            dump_path=save_error(
                cfg,
                stats,
                message="课程列表第 1 页缺少总数/页数",
                course_id=None,
                context={"page": 1, "parsed": first},
                html=html,
            ),
        )
    if pages != (total + PAGE_SIZE - 1) // PAGE_SIZE:
        raise SchemaMismatch(
            f"课程总数 {total} 与页数 {pages} 不匹配",
            context={"page": 1},
            dump_path=save_error(
                cfg,
                stats,
                message=f"课程总数 {total} 与页数 {pages} 不匹配",
                course_id=None,
                context={"page": 1, "parsed": first},
                html=html,
            ),
        )
    try:
        _validate_list_page(1, total, pages, first["items"])
    except ICourseError as exc:
        raise SchemaMismatch(
            str(exc),
            context=exc.context,
            dump_path=save_error(
                cfg,
                stats,
                message=str(exc),
                course_id=None,
                context=exc.context,
                html=html,
            ),
        ) from exc

    ids: list[str] = [item["course_id"] for item in first["items"]]
    wanted_pages = pages
    if cfg.limit_pages and cfg.limit_pages > 0:
        wanted_pages = min(pages, cfg.limit_pages)

    for page in range(2, wanted_pages + 1):
        if stop.is_set():
            raise CrawlAborted("停止标志已设置")
        html, _resp = fetch_html(
            pool, limiter, stats, stop, cfg, "/course/", {"page": page}
        )
        listing = parse_course_list(html)
        if listing.get("total") != total or listing.get("pages") != pages:
            message = (
                f"课程列表第 {page} 页总数/页数与第 1 页不一致："
                f"{listing.get('total')}/{listing.get('pages')} != {total}/{pages}"
            )
            raise SchemaMismatch(
                message,
                context={"page": page},
                dump_path=save_error(
                    cfg,
                    stats,
                    message=message,
                    course_id=None,
                    context={"page": page, "parsed": listing},
                    html=html,
                ),
            )
        if listing.get("page") != page:
            message = f"请求第 {page} 页，页面标注第 {listing.get('page')} 页"
            raise SchemaMismatch(
                message,
                context={"page": page},
                dump_path=save_error(
                    cfg,
                    stats,
                    message=message,
                    course_id=None,
                    context={"page": page, "parsed": listing},
                    html=html,
                ),
            )
        try:
            _validate_list_page(page, total, pages, listing["items"])
        except ICourseError as exc:
            raise SchemaMismatch(
                str(exc),
                context=exc.context,
                dump_path=save_error(
                    cfg,
                    stats,
                    message=str(exc),
                    course_id=None,
                    context=exc.context,
                    html=html,
                ),
            ) from exc
        ids.extend(item["course_id"] for item in listing["items"])

    # 去重但保持顺序
    seen: set[str] = set()
    unique_ids: list[str] = []
    for cid in ids:
        if cid not in seen:
            seen.add(cid)
            unique_ids.append(cid)

    complete = wanted_pages >= pages
    limited = len(unique_ids) < total
    info = {
        "source": "list",
        "total": total,
        "pages": pages,
        "fetched_pages": wanted_pages,
        "complete": complete,
        "limited": limited,
    }
    atomic_write_json(
        cfg.ids_path,
        {
            "version": VERSION,
            "fetched_at": now_iso(),
            **info,
            "ids": unique_ids,
        },
        stats,
    )
    return unique_ids, info


# --------------------------------------------------------------------------- #
# 课程抓取
# --------------------------------------------------------------------------- #


def course_complete(course_path: Path, reviews_dir: Path) -> bool:
    try:
        data = json.loads(course_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    review_ids = data.get("review_ids")
    if not isinstance(review_ids, list):
        return False
    reported = data.get("review_count")
    if reported and not review_ids:
        return False
    return all((reviews_dir / f"{rid}.json").is_file() for rid in review_ids)


def crawl_course(
    course_id: str,
    cfg: Config,
    pool: SessionPool,
    limiter: RateLimiter,
    stats: Stats,
    stop: threading.Event,
) -> None:
    stats.begin_task()
    try:
        if stop.is_set():
            raise CrawlAborted("停止标志已设置")
        course_path = cfg.courses_dir / f"{course_id}.json"
        reviews_dir = cfg.reviews_dir / course_id
        if cfg.resume and course_complete(course_path, reviews_dir):
            stats.note_skipped()
            return

        html: str | None = None
        try:
            html, _response = fetch_html(
                pool, limiter, stats, stop, cfg, f"/course/{course_id}/"
            )
        except FetchError as exc:
            if stop.is_set():
                raise CrawlAborted(str(exc)) from exc
            dump = save_error(
                cfg,
                stats,
                message=str(exc),
                course_id=course_id,
                context={"path": exc.path, "status": exc.status},
                html=exc.body,
                kind="fetch_error",
            )
            exc.dump_path = dump
            stop.set()
            raise exc

        if stop.is_set():
            raise CrawlAborted("停止标志已设置")

        try:
            course = parse_course_page(html, course_id=course_id, strict=True)
        except ICourseError as exc:
            if stop.is_set():
                raise CrawlAborted(str(exc)) from exc
            context = dict(exc.context)
            review_id = context.get("review_id") or (
                (REVIEW_ID_RE.search(str(exc)) or [None, None])[1]
            )
            if review_id:
                context.setdefault("review_id", str(review_id))
            partial_course = _partial_course(html, course_id)
            partial_review = _find_partial_review(
                html, course_id, context.get("review_id")
            )
            dump = save_error(
                cfg,
                stats,
                message=str(exc),
                course_id=course_id,
                context=context,
                html=html,
                partial_course=partial_course,
                partial_review=partial_review,
            )
            stop.set()
            raise SchemaMismatch(
                str(exc),
                course_id=course_id,
                context=context,
                dump_path=dump,
            ) from exc

        reviews = course.pop("reviews")
        fetched_at = now_iso()
        review_index: list[dict[str, Any]] = []
        comment_total = 0
        for review in reviews:
            if stop.is_set():
                raise CrawlAborted("停止标志已设置")
            review_id = review["review_id"]
            review["course_id"] = course_id
            review["course_title"] = course["title"]
            review["comments_parsed"] = len(review.get("comments", []))
            review["comments_reported"] = review.get("comment_count")
            review["_crawl"] = {
                "fetched_at": fetched_at,
                "url": review["url"],
                "http_status": 200,
                "source": "course_page",
            }
            write_new = atomic_write_json(
                reviews_dir / f"{review_id}.json", review, stats
            )
            comment_total += len(review.get("comments", []))
            review_index.append(
                {
                    "review_id": review_id,
                    "author": review.get("author"),
                    "author_id": review.get("author_id"),
                    "anonymous": review.get("anonymous"),
                    "rating": review.get("rating"),
                    "term": review.get("term"),
                    "created_at": review.get("created_at"),
                    "upvotes": review.get("upvotes"),
                    "comment_count": review.get("comment_count"),
                    "comments_parsed": review["comments_parsed"],
                    "path": f"reviews/{course_id}/{review_id}.json",
                    "new": write_new,
                }
            )

        course["review_ids"] = [review["review_id"] for review in reviews]
        course["review_index"] = review_index
        course["_crawl"] = {
            "fetched_at": fetched_at,
            "url": f"{BASE_URL}/course/{course_id}/",
            "http_status": 200,
            "reviews_parsed": len(reviews),
            "reviews_reported": course.get("review_count"),
            "comments_parsed": comment_total,
            "page_bytes": len(html.encode("utf-8")),
        }
        atomic_write_json(course_path, course, stats)
        stats.note_course(len(reviews), comment_total)
    finally:
        stats.end_task()


# --------------------------------------------------------------------------- #
# 抓取主循环
# --------------------------------------------------------------------------- #


def crawl_all(
    ids: list[str],
    cfg: Config,
    pool: SessionPool,
    limiter: RateLimiter,
    stats: Stats,
    stop: threading.Event,
) -> None:
    future_map: dict[Future[None], str] = {}
    fatal: BaseException | None = None
    with ThreadPoolExecutor(max_workers=cfg.workers, thread_name_prefix="course") as executor:
        for course_id in ids:
            if stop.is_set():
                break
            future_map[executor.submit(
                crawl_course, course_id, cfg, pool, limiter, stats, stop
            )] = course_id
        try:
            for future in as_completed(future_map):
                if stop.is_set() and fatal is not None:
                    break
                try:
                    future.result()
                except CrawlAborted:
                    continue
                except (SchemaMismatch, FetchError) as exc:
                    fatal = exc
                    stats.note_error()
                    stop.set()
                    for pending in future_map:
                        if not pending.done():
                            pending.cancel()
                    break
                except Exception as exc:  # 非预期异常也停止
                    fatal = exc
                    stats.note_error()
                    stop.set()
                    for pending in future_map:
                        if not pending.done():
                            pending.cancel()
                    break
        finally:
            if fatal is not None:
                for pending in future_map:
                    if not pending.done():
                        pending.cancel()
    if fatal is not None:
        raise fatal


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #


def _parse_course_ids(raw: str) -> list[str]:
    values = [value for value in re.split(r"[,;\s]+", raw.strip()) if value]
    for value in values:
        if not value.isdigit():
            raise argparse.ArgumentTypeError(f"非法课程 ID：{value!r}")
    return values


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="icourse.club 全站只读抓取器（课程 / 点评 / 评论）"
    )
    parser.add_argument("--data-dir", default="data", help="数据目录，默认 ./data")
    parser.add_argument("--username", help="用户名；也可用 ICOURSE_USERNAME")
    parser.add_argument("--password", help="密码；也可用 ICOURSE_PASSWORD")
    parser.add_argument("--workers", type=int, default=8, help="课程并发线程数，默认 8")
    parser.add_argument(
        "--rps", type=float, default=2.0, help="全局请求速率，0 表示不限速，默认 2"
    )
    parser.add_argument(
        "--burst", type=int, default=0, help="令牌桶容量，默认 max(1, rps)"
    )
    parser.add_argument("--timeout", type=float, default=30.0, help="单请求超时秒数")
    parser.add_argument("--retries", type=int, default=3, help="失败重试次数")
    parser.add_argument("--backoff", type=float, default=1.0, help="重试基础退避秒数")
    parser.add_argument("--refresh", type=float, default=1.0, help="实时面板刷新秒数")
    parser.add_argument(
        "--limit-pages", type=int, default=0, help="只发现前 N 页课程；0 表示全部"
    )
    parser.add_argument(
        "--limit-courses", type=int, default=0, help="只抓取前 N 门课程；0 表示全部"
    )
    parser.add_argument(
        "--course-ids", type=_parse_course_ids, default=[], help="直接指定课程 ID，逗号分隔"
    )
    parser.add_argument("--resume", action="store_true", help="跳过已完整抓取的课程")
    parser.add_argument("--quiet", action="store_true", help="关闭实时面板")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = build_parser().parse_args(list(argv) if argv is not None else None)
    username = args.username or os.environ.get("ICOURSE_USERNAME")
    password = args.password or os.environ.get("ICOURSE_PASSWORD")
    if not username or not password:
        sys.stderr.write("错误：必须提供用户名和密码（参数或 ICOURSE_USERNAME/ICOURSE_PASSWORD）\n")
        return 1
    if args.workers < 1:
        sys.stderr.write("错误：--workers 必须 >= 1\n")
        return 1
    if args.rps < 0 or args.timeout <= 0 or args.retries < 0 or args.backoff < 0:
        sys.stderr.write("错误：限流/超时/重试参数非法\n")
        return 1
    if args.refresh <= 0:
        sys.stderr.write("错误：--refresh 必须 > 0\n")
        return 1
    if args.limit_pages < 0 or args.limit_courses < 0:
        sys.stderr.write("错误：--limit-pages/--limit-courses 不能为负数\n")
        return 1

    cfg = Config(
        data_dir=Path(args.data_dir),
        username=username,
        password=password,
        workers=args.workers,
        rps=args.rps,
        burst=args.burst,
        timeout=args.timeout,
        retries=args.retries,
        backoff=args.backoff,
        refresh=args.refresh,
        limit_pages=args.limit_pages,
        limit_courses=args.limit_courses,
        course_ids=args.course_ids,
        resume=args.resume,
        quiet=args.quiet,
    )
    stats = Stats(cfg.data_dir)
    stop = threading.Event()
    reporter = Reporter(stats, cfg.refresh, cfg.quiet)
    manifest: dict[str, Any] = {
        "version": VERSION,
        "started_at": now_iso(),
        "status": "starting",
        "base_url": BASE_URL,
        "config": {
            key: (str(value) if isinstance(value, Path) else value)
            for key, value in cfg.__dict__.items()
            if key not in {"password"}
        },
        "discovery": None,
        "error": None,
    }

    status = "running"
    exit_code = 0
    fatal: BaseException | None = None

    try:
        client = ICourseClient(timeout=cfg.timeout)

        def _count_login_response(response: requests.Response, *_args: Any, **_kwargs: Any) -> None:
            stats.note_request()
            stats.note_bytes(len(response.content))

        client.session.hooks["response"].append(_count_login_response)
        client.login(username, password)
        if not client.user_id:
            sys.stderr.write("错误：登录后未能读取到 user_id\n")
            return 1
        print(f"已登录：user_id={client.user_id}", file=sys.stderr)
        pool = SessionPool(client.session)
        limiter = RateLimiter(cfg.rps, cfg.burst)

        cfg.data_dir.mkdir(parents=True, exist_ok=True)
        atomic_write_json(cfg.manifest_path, manifest, stats)
        reporter.start()

        ids, discovery = discover_courses(cfg, pool, limiter, stats, stop)
        if cfg.limit_courses and cfg.limit_courses > 0:
            ids = ids[: cfg.limit_courses]
        if not ids:
            raise SchemaMismatch("没有发现任何课程")
        stats.set_total_courses(len(ids))
        manifest["discovery"] = discovery
        manifest["crawl"] = {
            "courses_requested": len(ids),
            "limit_courses": cfg.limit_courses,
        }

        print(
            f"发现课程：{discovery.get('total')} 门，"
            f"本次抓取 {len(ids)} 门（source={discovery.get('source')}）",
            file=sys.stderr,
        )
        crawl_all(ids, cfg, pool, limiter, stats, stop)
        status = "completed"
        exit_code = 0
    except KeyboardInterrupt:
        stop.set()
        status = "interrupted"
        exit_code = 130
        sys.stderr.write("\n收到 Ctrl-C，正在停止...\n")
    except SchemaMismatch as exc:
        stop.set()
        fatal = exc
        status = "schema_mismatch"
        exit_code = 2
    except FetchError as exc:
        stop.set()
        fatal = exc
        status = "fetch_error"
        exit_code = 3
    except ICourseError as exc:
        stop.set()
        fatal = exc
        status = "auth_error"
        exit_code = 1
    except Exception as exc:
        stop.set()
        fatal = exc
        status = "error"
        exit_code = 4
        traceback.print_exc()
    finally:
        stop.set()
        reporter.stop()
        manifest["finished_at"] = now_iso()
        manifest["status"] = status
        manifest["stats"] = stats.summary()
        if isinstance(fatal, SchemaMismatch):
            manifest["error"] = {
                "type": "schema_mismatch",
                "message": str(fatal),
                "course_id": fatal.course_id,
                "context": fatal.context,
                "dump_path": str(fatal.dump_path) if fatal.dump_path else None,
            }
        elif isinstance(fatal, FetchError):
            manifest["error"] = {
                "type": "fetch_error",
                "message": str(fatal),
                "path": fatal.path,
                "status": fatal.status,
            }
        elif fatal is not None:
            manifest["error"] = {"type": type(fatal).__name__, "message": str(fatal)}
        try:
            cfg.data_dir.mkdir(parents=True, exist_ok=True)
            atomic_write_json(cfg.manifest_path, manifest, stats)
        except Exception:
            traceback.print_exc()

        summary = stats.summary()
        print(
            "\n=== 抓取结束 ===\n"
            f"状态: {status}\n"
            f"耗时: {fmt_duration(summary['elapsed_seconds'])}\n"
            f"课程: {summary['courses_done']}/{summary['total_courses'] or '?'} "
            f"(跳过 {summary['skipped']})\n"
            f"点评(本次): {summary['reviews']:,}  评论(本次): {summary['comments']:,}\n"
            f"请求: {summary['requests']:,} / {human_bytes(summary['bytes'])}\n"
            f"文件: {summary['files']:,} / {human_bytes(summary['file_bytes'])}\n"
            f"数据目录: {cfg.data_dir.resolve()}"
        )

        if isinstance(fatal, SchemaMismatch):
            context = fatal.context or {}
            print("\n!!! 数据结构不符合预期，已主动停止抓取 !!!", file=sys.stderr)
            print(f"课程: {fatal.course_id or '-'}", file=sys.stderr)
            if fatal.course_id:
                print(f"课程 URL: {BASE_URL}/course/{fatal.course_id}/", file=sys.stderr)
            if context.get("review_id"):
                print(f"点评: {context['review_id']}", file=sys.stderr)
            if context.get("comment_index"):
                print(f"评论序号: {context['comment_index']}", file=sys.stderr)
            print(f"原因: {fatal}", file=sys.stderr)
            if fatal.dump_path:
                print(f"错误详情: {fatal.dump_path}", file=sys.stderr)
                html_path = fatal.dump_path.with_suffix(".html")
                if html_path.exists():
                    print(f"原始页面: {html_path}", file=sys.stderr)
        elif isinstance(fatal, FetchError):
            print("\n!!! 请求失败，已停止 !!!", file=sys.stderr)
            print(f"路径: {fatal.path}", file=sys.stderr)
            print(f"状态: {fatal.status}", file=sys.stderr)
            print(f"原因: {fatal}", file=sys.stderr)
            if fatal.dump_path:
                print(f"错误详情: {fatal.dump_path}", file=sys.stderr)
        elif fatal is not None:
            print(f"\n!!! 抓取失败，已停止 !!!\n原因: {fatal}", file=sys.stderr)

    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
