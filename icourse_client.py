"""USTC 评课社区（icourse.club）只读数据客户端。

站点是 Django 服务端渲染：

* 课程列表、课程详情、点评、评论都直接渲染在 HTML 里；
* 没有公开的课程/点评 JSON API（``/api/`` 返回 404）；
* 仅评论列表有一个返回 HTML 片段的 GET 接口 ``/review/comments/?review_id=``；
* 登录走 ``/signin/``，成功后使用 Django 签名 session cookie；
* 点评正文是 CKEditor 5 生成的 HTML（不是 Markdown），公式以
  ``<span class="math-tex">\\(...\\)</span>`` 等形式存储。

本模块只实现只读请求（GET + 登录 POST），不包含点赞、发评、删评等写接口。
"""

from __future__ import annotations

import argparse
import base64
import json
import math
import os
import re
import sys
import zlib
from datetime import datetime, timezone
from typing import Any, Iterable
from urllib.parse import parse_qs, urljoin, urlparse

import requests
from bs4 import BeautifulSoup, Tag

BASE_URL = "https://icourse.club"
USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0 Safari/537.36 icourse-readonly-parser"
)

# 点评中的四项三选一评价，值 -> 序号（与提交表单一致）
POLL_VALUES: dict[str, dict[str, int]] = {
    "difficulty": {"简单": 1, "中等": 2, "困难": 3},
    "homework": {"不多": 1, "中等": 2, "超多": 3},
    "grading": {"超好": 1, "一般": 2, "杀手": 3},
    "gain": {"很多": 1, "一般": 2, "没有": 3},
}
POLL_LABELS = {
    "课程难度": "difficulty",
    "作业多少": "homework",
    "给分好坏": "grading",
    "收获大小": "gain",
}
IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".bmp", ".avif"}
REVIEW_TIME_FMT = "%m/%d/%Y %H:%M:%S"
PAGE_SIZE = 10


class ICourseError(RuntimeError):
    """站点返回了非预期内容。"""

    def __init__(self, message: str, *, context: dict[str, Any] | None = None) -> None:
        super().__init__(message)
        self.context = context or {}


# --------------------------------------------------------------------------- #
# 通用工具
# --------------------------------------------------------------------------- #


def _clean(text: str) -> str:
    """压缩空白，去掉 NBSP / 全角空格。"""
    text = text.replace("\xa0", " ").replace("\u3000", " ")
    return re.sub(r"\s+", " ", text).strip()


def _iso_utc(text: str) -> str | None:
    """``07/14/2025 08:35:51``（站点按 UTC 输出）-> ISO 8601。"""
    text = _clean(text)
    if not text:
        return None
    try:
        dt = datetime.strptime(text, REVIEW_TIME_FMT).replace(tzinfo=timezone.utc)
    except ValueError:
        return None
    return dt.isoformat()


def _absolute(url: str | None) -> str | None:
    if not url:
        return None
    return urljoin(BASE_URL, url)


def _balanced_div_inner(html: str, pos: int) -> str:
    """从 ``pos``（div 开始标签之后）取出配对的 div 内部 HTML。

    CKEditor 生成的正文里嵌套了 ``<p><div>`` 等非法结构，正则非贪婪会在
    第一个 ``</div>`` 截断，所以这里做 div 深度扫描，保证拿到完整正文。
    """
    depth = 1
    tag_re = re.compile(r"<(/?)div\b[^>]*>", re.I)
    for match in tag_re.finditer(html, pos):
        if match.group(1):
            depth -= 1
            if depth == 0:
                return html[pos : match.start()]
        elif not match.group(0).rstrip().endswith("/>"):
            depth += 1
    return html[pos:]


def _extract_div_by_id(html: str, element_id: str) -> str | None:
    pattern = re.compile(
        rf'<div\b[^>]*\bid="{re.escape(element_id)}"[^>]*>', re.I
    )
    match = pattern.search(html)
    if not match:
        return None
    return _balanced_div_inner(html, match.end())


def _html_to_text(fragment: str) -> str:
    """HTML -> 纯文本；保留段落/换行，去掉标签。"""
    soup = BeautifulSoup(fragment, "lxml")
    for br in soup.find_all("br"):
        br.replace_with("\n")
    for tag in soup.find_all(
        ["p", "div", "li", "h1", "h2", "h3", "h4", "h5", "h6", "tr", "blockquote", "pre"]
    ):
        tag.insert_after("\n")
    text = soup.get_text()
    text = text.replace("\xa0", " ").replace("\u3000", " ")
    text = re.sub(r"[ \t]+\n", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def _star_rating(header: Tag) -> float | None:
    """点评星级：实心 1 分，半星 0.5 分；没有星级节点表示未评分。"""
    rating = 0.0
    found = False
    for span in header.find_all("span", class_="glyphicon"):
        classes = span.get("class") or []
        if "glyphicon-star" in classes:
            rating += 1.0
            found = True
        elif "glyphicon-star-half" in classes:
            rating += 0.5
            found = True
        elif "glyphicon-star-empty" in classes:
            found = True
    return rating if found else None


def _parse_poll_list(node: Tag | None) -> dict[str, Any]:
    polls: dict[str, Any] = {}
    if node is None:
        return polls
    for li in node.find_all("li"):
        label, sep, value = li.get_text(strip=True).partition("：")
        if not sep:
            continue
        key = POLL_LABELS.get(_clean(label))
        if not key:
            continue
        value = _clean(value)
        polls[key] = {"label": value, "value": POLL_VALUES[key].get(value)}
    return polls


def _query_param(href: str, name: str) -> str | None:
    values = parse_qs(urlparse(href).query).get(name)
    return values[0] if values else None


def _parse_options(soup: BeautifulSoup, name: str, param: str) -> list[dict[str, Any]]:
    """解析筛选下拉框：term / rating / sort_by。"""
    select = soup.find("select", attrs={"name": name})
    if select is None:
        return []
    options: list[dict[str, Any]] = []
    for option in select.find_all("option"):
        text = _clean(option.get_text())
        value = _query_param(option.get("value", ""), param)
        if value is None:
            continue
        count_match = re.search(r"\((\d+)\)", text)
        entry: dict[str, Any] = {
            "value": value,
            "label": re.sub(r"\s*\(\d+\)$", "", text).strip(),
        }
        if count_match:
            entry["count"] = int(count_match.group(1))
        options.append(entry)
    return options


def _term_code(term_label: str | None) -> str | None:
    """``2025秋`` -> ``20251``。"""
    if not term_label:
        return None
    match = re.search(r"(\d{4})\s*([秋冬春夏])", term_label)
    if not match:
        return None
    semester = {"秋": "1", "春": "2", "夏": "3"}[match.group(2)]
    return match.group(1) + semester


# --------------------------------------------------------------------------- #
# 登录 / 会话
# --------------------------------------------------------------------------- #


def _csrf_token(html: str) -> str | None:
    soup = BeautifulSoup(html, "lxml")
    node = soup.find("input", attrs={"name": "csrf_token"})
    return node.get("value") if node else None


def decode_session_cookie(value: str) -> dict[str, Any]:
    """解码 Django 签名 cookie session 的 payload（不校验签名）。

    站点 cookie 形如 ``.<base64(zlib(json))>.<timestamp>.<signature>``。
    payload 里有 ``_user_id``、``csrf_token``、``_fresh`` 等字段。
    """
    parts = value.split(".")
    payload = parts[1] if parts and parts[0] == "" else parts[0]
    raw = base64.urlsafe_b64decode(payload + "=" * (-len(payload) % 4))
    if raw[:1] == b"x":
        raw = zlib.decompress(raw)
    return json.loads(raw.decode("utf-8"))


class ICourseClient:
    """icourse.club 只读客户端。"""

    def __init__(self, timeout: float = 30.0) -> None:
        self.timeout = timeout
        self.session = requests.Session()
        self.session.headers.update(
            {
                "User-Agent": USER_AGENT,
                "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
                "Referer": BASE_URL + "/",
            }
        )

    # -- 认证 ------------------------------------------------------------- #

    def login(self, username: str, password: str) -> dict[str, Any]:
        """登录并保存 session cookie。

        站点 CSRF 使用 session 存储（没有独立的 csrftoken cookie）：
        token 既渲染在 ``input[name=csrf_token]``，也通过 ``X-CSRFToken`` 头提交。
        """
        home = self.session.get(BASE_URL + "/", timeout=self.timeout)
        home.raise_for_status()
        token = _csrf_token(home.text)
        if not token:
            raise ICourseError("首页未找到 csrf_token，站点结构可能已变化")

        response = self.session.post(
            BASE_URL + "/signin/",
            params={"next": "/", "ajax": "True"},
            data={"csrf_token": token, "username": username, "password": password},
            headers={
                "X-CSRFToken": token,
                "X-Requested-With": "XMLHttpRequest",
                "Referer": BASE_URL + "/",
            },
            timeout=self.timeout,
        )
        response.raise_for_status()
        try:
            payload = response.json()
        except ValueError as exc:  # 缺 CSRF 时站点返回 400 HTML
            raise ICourseError(
                f"登录返回非 JSON（HTTP {response.status_code}），CSRF 可能失效"
            ) from exc
        if payload.get("status") != 200:
            raise ICourseError(payload.get("msg") or f"登录失败：{payload}")
        return payload

    def session_info(self) -> dict[str, Any] | None:
        cookie = self.session.cookies.get("session")
        if not cookie:
            return None
        try:
            return decode_session_cookie(cookie)
        except (ValueError, zlib.error, json.JSONDecodeError):
            return None

    @property
    def user_id(self) -> str | None:
        info = self.session_info() or {}
        value = info.get("_user_id")
        return str(value) if value is not None else None

    # -- 请求 ------------------------------------------------------------- #

    def _get(self, path: str, params: dict[str, Any] | None = None) -> str:
        response = self.session.get(
            BASE_URL + path, params=params, timeout=self.timeout
        )
        response.raise_for_status()
        return response.text

    # -- 页面 ------------------------------------------------------------- #

    def get_course(
        self,
        course_id: int | str,
        *,
        sort_by: str | None = None,
        term: str | None = None,
        rating: int | None = None,
    ) -> dict[str, Any]:
        params = {}
        if sort_by:
            params["sort_by"] = sort_by
        if term:
            params["term"] = term
        if rating:
            params["rating"] = rating
        html = self._get(f"/course/{course_id}/", params or None)
        return parse_course_page(html, course_id=str(course_id))

    def list_courses(
        self,
        *,
        q: str = "",
        course_type: str | None = None,
        sort_by: str | None = None,
        page: int = 1,
    ) -> dict[str, Any]:
        params: dict[str, Any] = {"q": q, "page": page}
        if course_type:
            params["course_type"] = course_type
        if sort_by:
            params["sort_by"] = sort_by
        return parse_course_list(self._get("/course/", params))

    def search_courses(self, q: str, *, page: int = 1) -> dict[str, Any]:
        return parse_course_list(self._get("/search/", {"q": q, "page": page}))

    def search_reviews(self, q: str, *, page: int = 1) -> dict[str, Any]:
        return parse_review_feed(
            self._get("/search-reviews/", {"q": q, "page": page})
        )

    def latest_reviews(self, *, page: int = 1, q: str = "") -> dict[str, Any]:
        params: dict[str, Any] = {"page": page}
        if q:
            params["q"] = q
        return parse_review_feed(self._get("/latest_reviews", params))

    def get_comments(self, review_id: int | str) -> list[dict[str, Any]]:
        html = self._get("/review/comments/", {"review_id": review_id})
        return parse_comments_fragment(html)

    def user_reviews(self, user_id: int | str, *, page: int = 1) -> dict[str, Any]:
        return parse_user_reviews(
            self._get(f"/user/{user_id}/reviews", {"page": page})
        )


# --------------------------------------------------------------------------- #
# 课程详情
# --------------------------------------------------------------------------- #


def parse_course_page(
    html: str, *, course_id: str, strict: bool = False
) -> dict[str, Any]:
    soup = BeautifulSoup(html, "lxml")
    main = soup.find("div", class_="col-md-8 inline-h3")
    if main is None:
        raise ICourseError("未找到课程主栏，页面结构可能已变化")

    title_node = main.find("span", class_="blue h3")
    title = _clean(title_node.get_text()) if title_node else None
    teacher_node = main.find("span", class_="h3 blue mobile")
    teacher_text = _clean(teacher_node.get_text()).strip("（）()") if teacher_node else ""

    terms: list[str] = []
    course_code = None
    meta_node = main.select_one("span.small.grey.align-bottom.desktop")
    if meta_node:
        meta_text = _clean(meta_node.get_text())
        terms = re.findall(r"\d{4}[秋冬春夏]", meta_text)
        code_match = re.search(r"课程号[：:]\s*(\S+)", meta_text)
        if code_match:
            course_code = code_match.group(1)

    rating_box = main.find("div", class_="desktop ud-pd-sm blue")
    rating = review_rating_count = None
    if rating_box:
        score_node = rating_box.find("span", class_="rl-pd-sm h4")
        if score_node:
            try:
                rating = float(_clean(score_node.get_text()))
            except ValueError:
                pass
        count_node = rating_box.find("span", class_="rl-pd-sm text-muted")
        if count_node:
            count_match = re.search(r"(\d+)", count_node.get_text())
            if count_match:
                review_rating_count = int(count_match.group(1))

    polls = _parse_poll_list(
        main.find("ul", class_="text-muted list-inline list-unstyled ud-pd-sm")
    )

    info: dict[str, str] = {}
    credits = None
    info_table = main.find("table", class_="table-condensed")
    if info_table:
        for td in info_table.find_all("td"):
            strong = td.find("strong")
            if strong is None:
                continue
            label = _clean(strong.get_text()).rstrip("：:")
            full = _clean(td.get_text())
            value = full.replace(_clean(strong.get_text()), "", 1).lstrip("：: ")
            if label:
                info[label] = value
                if label == "学分":
                    number = re.search(r"[\d.]+", value)
                    if number:
                        credits = float(number.group())

    homepage = None
    home_strong = main.find(
        lambda tag: tag.name == "strong" and "课程主页" in tag.get_text()
    )
    if home_strong is not None:
        home_box = home_strong.parent
        link = home_box.find("a", href=True) if home_box else None
        if link:
            homepage = _absolute(link["href"])

    teachers = []
    for node in soup.select("div.col-md-4 h3.blue a[href^='/teacher/']"):
        match = re.search(r"/teacher/(\d+)/", node.get("href", ""))
        teachers.append(
            {
                "teacher_id": match.group(1) if match else None,
                "name": _clean(node.get_text()),
                "url": _absolute(node.get("href")),
            }
        )

    intro_html = _extract_div_by_id(html, "course-intro")
    summary_html = _extract_div_by_id(html, "course-summary")

    review_count = None
    review_header = soup.find("div", class_="review-header")
    if review_header:
        count_match = re.search(r"(\d+)\s*条点评", review_header.get_text())
        if count_match:
            review_count = int(count_match.group(1))

    term_options = _parse_options(soup, "term", "term")
    rating_options = _parse_options(soup, "rating", "rating")
    sort_options = _parse_options(soup, "sort_by", "sort_by")
    term_map = {option["label"]: option["value"] for option in term_options}

    deleted_reviews = hidden_comments = None
    page_text = soup.get_text(" ")
    match = re.search(r"本课程有\s*(\d+)\s*位用户曾删除过点评", page_text)
    if match:
        deleted_reviews = int(match.group(1))
    match = re.search(r"本页面有\s*(\d+)\s*条评论因违反.*?被隐藏", page_text)
    if match:
        hidden_comments = int(match.group(1))

    meta = soup.find("meta", attrs={"property": "og:description"})
    meta_description = meta.get("content") if meta else None

    reviews = [
        parse_review(
            node, html, course_id=course_id, term_map=term_map, strict=strict
        )
        for node in soup.find_all("div", class_="review", id=re.compile(r"^review-\d+$"))
    ]

    if strict:
        if not title:
            raise ICourseError("课程页缺少标题", context={"course_id": course_id})
        if '/logout/' not in html:
            raise ICourseError(
                "课程页缺少登录态（session 可能已失效）",
                context={"course_id": course_id},
            )
        if 'id="review-anchor"' not in html and (review_count or reviews):
            raise ICourseError(
                "课程页缺少点评区（结构可能已变化）",
                context={"course_id": course_id},
            )
        if review_count is not None and len(reviews) > review_count:
            raise ICourseError(
                f"解析到 {len(reviews)} 条点评，超过页面标注的 {review_count} 条",
                context={"course_id": course_id},
            )
        if review_count and not reviews:
            raise ICourseError(
                f"页面标注 {review_count} 条点评，但未解析到任何点评"
                "（可能登录态/学生权限不足）",
                context={"course_id": course_id},
            )

    return {
        "course_id": course_id,
        "url": f"{BASE_URL}/course/{course_id}/",
        "title": title,
        "teacher_text": teacher_text,
        "teachers": teachers,
        "course_code": course_code,
        "terms": terms,
        "rating": rating,  # 0-10 分
        "rating_count": review_rating_count,
        "review_count": review_count,
        "polls": polls,
        "info": info,
        "credits": credits,
        "homepage": homepage,
        "meta_description": meta_description,
        "intro_html": intro_html,
        "intro_text": _html_to_text(intro_html) if intro_html else None,
        "ai_summary_html": summary_html,
        "ai_summary_text": _html_to_text(summary_html) if summary_html else None,
        "term_options": term_options,
        "rating_options": rating_options,
        "sort_options": sort_options,
        "stats": _parse_review_stats(soup),
        "deleted_reviews": deleted_reviews,
        "hidden_comments": hidden_comments,
        "reviews": reviews,
    }


def _parse_review_stats(soup: BeautifulSoup) -> list[dict[str, Any]]:
    script = None
    for node in soup.find_all("script"):
        text = node.string or node.get_text()
        if "course-review-stats" in text and "Highcharts.chart" in text:
            script = text
            break
    if not script:
        return []
    categories_match = re.search(r"categories:\s*\[(.*?)\]", script, re.S)
    avg_match = re.search(r"name:\s*'平均分'.*?data:\s*\[(.*?)\]", script, re.S)
    count_match = re.search(r"name:\s*'点评数量'.*?data:\s*\[(.*?)\]", script, re.S)
    if not categories_match:
        return []
    terms = re.findall(r"'([^']+)'", categories_match.group(1))
    averages = [
        float(value) for value in re.findall(r"\d+(?:\.\d+)?", avg_match.group(1))
    ] if avg_match else []
    counts = [
        int(value) for value in re.findall(r"\d+", count_match.group(1))
    ] if count_match else []
    return [
        {
            "term": term,
            "avg_score": averages[index] if index < len(averages) else None,
            "review_count": counts[index] if index < len(counts) else None,
        }
        for index, term in enumerate(terms)
    ]


# --------------------------------------------------------------------------- #
# 单条点评 / 评论
# --------------------------------------------------------------------------- #


def parse_review(
    node: Tag,
    html: str,
    *,
    course_id: str,
    term_map: dict[str, str] | None = None,
    strict: bool = False,
) -> dict[str, Any]:
    review_id_match = re.search(r"(\d+)", node.get("id", ""))
    if not review_id_match:
        raise ICourseError("点评节点缺少 id")
    review_id = review_id_match.group(1)

    header = node.find("div", class_="blue ud-pd-sm")
    if header is None:
        raise ICourseError(f"点评 {review_id} 缺少头部")

    author_node = header.find("span", class_="right-pd-sm px16")
    author = author_id = None
    anonymous = False
    if author_node:
        link = author_node.find("a", href=re.compile(r"^/user/\d+"))
        if link:
            id_match = re.search(r"/user/(\d+)", link["href"])
            author_id = id_match.group(1) if id_match else None
            author = _clean(link.get_text())
        else:
            anonymous = True
            author = _clean(author_node.get_text())

    term_node = header.find("span", class_="left-pd-md")
    term = _clean(term_node.get_text()) if term_node else None
    labels = [_clean(label.get_text()) for label in header.find_all("span", class_="label")]

    polls = _parse_poll_list(
        node.find("ul", class_="text-muted list-inline list-unstyled top-pd-sm desktop")
    )

    content_html = _extract_div_by_id(html, f"review-content-{review_id}")
    if content_html is None:
        content_node = node.find("div", class_="review-content")
        content_html = content_node.decode_contents() if content_node else ""

    footer = node.find("div", class_="bm-pd-md grey")
    upvotes = comment_count = None
    created_at = updated_at = None
    if footer:
        upvote_node = footer.find("span", id=f"review-upvote-count-{review_id}")
        if upvote_node:
            try:
                upvotes = int(_clean(upvote_node.get_text()))
            except ValueError:
                pass
        comment_node = footer.find("span", id=f"review-comment-count-{review_id}")
        if comment_node:
            try:
                comment_count = int(_clean(comment_node.get_text()))
            except ValueError:
                pass
        times = [
            _iso_utc(span.get_text())
            for span in footer.find_all("span", class_="localtime")
        ]
        times = [value for value in times if value]
        if times:
            created_at = times[0]
        if len(times) > 1:
            updated_at = times[1]

    panel_html = _extract_div_by_id(html, f"review-{review_id}-comments")
    if strict and panel_html is None:
        raise ICourseError(
            "点评缺少评论区容器", context={"review_id": review_id}
        )
    comments = parse_comments_fragment(
        panel_html or "", strict=strict, review_id=review_id
    )

    if strict:
        if author_node is None or not author:
            raise ICourseError("点评缺少作者", context={"review_id": review_id})
        if not content_html or not content_html.strip():
            raise ICourseError("点评正文为空", context={"review_id": review_id})
        if footer is None:
            raise ICourseError("点评缺少底部信息", context={"review_id": review_id})
        if not created_at:
            raise ICourseError("点评缺少发布时间", context={"review_id": review_id})

    return {
        "review_id": review_id,
        "url": f"{BASE_URL}/course/{course_id}/#review-{review_id}",
        "author": author,
        "author_id": author_id,
        "anonymous": anonymous,
        "rating": _star_rating(header),  # 0-5 分；null = 未评分
        "term": term,
        "term_code": (term_map or {}).get(term) or _term_code(term),
        "labels": labels,
        "only_visible_to_student": "仅登录学生可见" in labels,
        "polls": polls,
        "content_html": content_html,
        "content_text": _html_to_text(content_html),
        "content": _content_features(content_html),
        "created_at": created_at,
        "updated_at": updated_at,
        "upvotes": upvotes,
        "comment_count": comment_count,
        "comments": comments,
    }


def _content_features(content_html: str) -> dict[str, Any]:
    soup = BeautifulSoup(content_html, "lxml")
    text = _html_to_text(content_html)

    inline_math = [
        _clean(span.get_text())
        for span in soup.find_all("span", class_="math-tex")
    ]
    display_math = bool(re.search(r"\\\[|[^\\]\$\$", text)) or bool(
        soup.find("span", class_="math-display")
    )

    images = []
    file_links = []
    external_links = []
    for img in soup.find_all("img"):
        url = _absolute(img.get("src"))
        if url:
            images.append(url)
    for link in soup.find_all("a", href=True):
        href = link["href"]
        if href.startswith("/uploads/files/"):
            path = urlparse(href).path
            if os.path.splitext(path)[1].lower() not in IMAGE_EXTS:
                file_links.append(_absolute(href))
        elif href.startswith("http"):
            external_links.append(href)

    return {
        "format": "html",  # CKEditor 5 输出的 HTML，不是 Markdown
        "has_inline_math": bool(inline_math) or "\\(" in text,
        "inline_math": inline_math,
        "has_display_math": display_math,
        "has_images": bool(images),
        "images": images,
        "file_links": file_links,
        "external_links": external_links,
        "has_table": bool(soup.find("table")),
        "has_code_block": bool(soup.find("pre")),
        "has_blockquote": bool(soup.find("blockquote")),
        "has_headings": bool(soup.find(re.compile(r"^h[1-6]$"))),
        "has_lists": bool(soup.find(["ul", "ol"])),
        "has_hr": bool(soup.find("hr")),
        "has_media_embed": bool(soup.find(["iframe", "oembed"])),
    }


def parse_comments_fragment(
    html: str, *, strict: bool = False, review_id: str | None = None
) -> list[dict[str, Any]]:
    soup = BeautifulSoup(html, "lxml")
    comments = []
    for comment_index, item in enumerate(
        soup.find_all("div", class_="ud-pd-sm solid"), start=1
    ):
        author_link = item.find("a", href=re.compile(r"^/user/\d+"))
        author = author_id = None
        if strict and author_link is None:
            raise ICourseError(
                f"第 {comment_index} 条评论缺少作者链接",
                context={"review_id": review_id, "comment_index": comment_index},
            )
        if author_link:
            match = re.search(r"/user/(\d+)", author_link["href"])
            author_id = match.group(1) if match else None
            author = _clean(author_link.get_text())

        content_span = None
        for span in item.find_all("span", recursive=False):
            if not span.get("class"):
                content_span = span
                break
        if content_span is None:
            if strict:
                raise ICourseError(
                    f"第 {comment_index} 条评论缺少正文节点",
                    context={"review_id": review_id, "comment_index": comment_index},
                )
            continue

        text = content_span.get_text().replace("\xa0", " ").strip()
        if strict and not text:
            raise ICourseError(
                f"第 {comment_index} 条评论正文为空",
                context={"review_id": review_id, "comment_index": comment_index},
            )
        mentions = []
        for link in content_span.find_all("a", href=re.compile(r"^/user/\d+")):
            match = re.search(r"/user/(\d+)", link["href"])
            mentions.append(
                {
                    "user_id": match.group(1) if match else None,
                    "name": _clean(link.get_text()).lstrip("＠@"),
                }
            )

        reply_to = None
        reply_match = re.match(r"^回复\s*[＠@]\s*([^:：]+)[:：]\s*", text)
        if reply_match:
            reply_to = _clean(reply_match.group(1))

        time_node = item.find("span", class_="localtime")
        if strict and time_node is None:
            raise ICourseError(
                f"第 {comment_index} 条评论缺少时间",
                context={"review_id": review_id, "comment_index": comment_index},
            )
        comments.append(
            {
                "author": author,
                "author_id": author_id,
                "content_html": content_span.decode_contents(),
                "content_text": text,
                "mentions": mentions,
                "reply_to": reply_to,
                "created_at": _iso_utc(time_node.get_text()) if time_node else None,
            }
        )
    return comments


# --------------------------------------------------------------------------- #
# 列表 / 搜索 / 动态
# --------------------------------------------------------------------------- #


def _total_pages(total: int | None, page: int, soup: BeautifulSoup) -> int:
    """总页数优先按总数/每页 10 条计算；分页条只展示窗口，不能当总页数。"""
    if total:
        return max(1, math.ceil(total / PAGE_SIZE))
    pages = [
        int(match.group(1))
        for link in soup.select("ul.pagination a[href]")
        if (match := re.search(r"[?&]page=(\d+)", link["href"]))
    ]
    return max(pages) if pages else page


def parse_course_list(html: str) -> dict[str, Any]:
    soup = BeautifulSoup(html, "lxml")
    page_text = _clean(soup.get_text(" "))
    total_match = re.search(r"共\s*(\d+)\s*门课（当前第\s*(\d+)\s*页）", page_text)
    total = int(total_match.group(1)) if total_match else None
    page = int(total_match.group(2)) if total_match else 1

    items = []
    for card in soup.find_all("div", class_="ud-pd-md dashed"):
        title_link = card.find("a", class_="px16", href=re.compile(r"^/course/\d+"))
        if title_link is None:
            continue
        course_id_match = re.search(r"/course/(\d+)", title_link["href"])
        title = _clean(title_link.get_text())
        name, teachers = _split_title(title)

        term_hint = card.find("span", class_="small text-muted")
        labels = [_clean(label.get_text()) for label in card.find_all("span", class_="label")]

        score_node = card.find("span", class_="rl-pd-sm h4")
        rating = None
        if score_node:
            try:
                rating = float(_clean(score_node.get_text()))
            except ValueError:
                pass
        count_node = card.find("span", class_="text-muted px12")
        rating_count = None
        if count_node:
            match = re.search(r"(\d+)", count_node.get_text())
            if match:
                rating_count = int(match.group(1))

        items.append(
            {
                "course_id": course_id_match.group(1) if course_id_match else None,
                "title": title,
                "name": name,
                "teachers": teachers,
                "url": _absolute(title_link["href"]),
                "term_hint": _clean(term_hint.get_text()) if term_hint else None,
                "labels": labels,
                "rating": rating,
                "rating_count": rating_count,
                "polls": _parse_poll_list(
                    card.find("ul", class_="text-muted list-inline list-unstyled")
                ),
            }
        )

    pages = _total_pages(total, page, soup)
    return {
        "total": total,
        "page": page,
        "page_size": PAGE_SIZE,
        "pages": pages,
        "has_next": page < pages,
        "items": items,
    }


def _split_title(title: str) -> tuple[str, list[str]]:
    """``数学分析(B1)（程艺）`` -> (``数学分析(B1)``, [``程艺``])。"""
    match = re.match(r"^(.*)（([^（）]+)）$", title)
    if not match:
        return title, []
    teachers = [part.strip() for part in match.group(2).split(",") if part.strip()]
    return match.group(1).strip(), teachers


def parse_review_feed(html: str) -> dict[str, Any]:
    soup = BeautifulSoup(html, "lxml")
    page_text = _clean(soup.get_text(" "))
    total_match = re.search(r"共\s*(\d+)\s*个点评（当前第\s*(\d+)\s*页）", page_text)
    total = int(total_match.group(1)) if total_match else None
    page = int(total_match.group(2)) if total_match else 1

    items = []
    for card in soup.find_all("div", class_="ud-pd-md dashed"):
        course_link = card.find(
            "a", href=re.compile(r"/course/\d+/#review-\d+")
        )
        if course_link is None:
            continue
        href_match = re.search(r"/course/(\d+)/#review-(\d+)", course_link["href"])
        if not href_match:
            continue
        author_link = card.find("a", href=re.compile(r"^/user/\d+"))
        author = author_id = None
        if author_link:
            id_match = re.search(r"/user/(\d+)", author_link["href"])
            author_id = id_match.group(1) if id_match else None
            author = _clean(author_link.get_text())
        anonymous = author is None and "匿名用户" in card.get_text()

        header = card.find("div", class_="grey bm-pd-md")
        action = None
        if header:
            header_text = _clean(header.get_text(" "))
            if "更新了点评" in header_text:
                action = "updated"
            elif "点评了" in header_text:
                action = "created"

        time_node = card.find("span", class_="localtime")
        excerpt = card.find("p", class_="review-content")
        if excerpt:
            for more in excerpt.find_all("a", href=re.compile("#review-")):
                more.extract()
        excerpt_html = excerpt.decode_contents() if excerpt else ""

        items.append(
            {
                "review_id": href_match.group(2),
                "course_id": href_match.group(1),
                "course_title": _clean(course_link.get_text()),
                "url": _absolute(course_link["href"]),
                "author": author,
                "author_id": author_id,
                "anonymous": anonymous,
                "action": action,
                "created_at": _iso_utc(time_node.get_text()) if time_node else None,
                "excerpt_html": excerpt_html,
                "excerpt_text": _html_to_text(excerpt_html),
            }
        )

    pages = _total_pages(total, page, soup)
    return {
        "total": total,
        "page": page,
        "page_size": PAGE_SIZE,
        "pages": pages,
        "has_next": page < pages,
        "items": items,
    }


def parse_user_reviews(html: str) -> dict[str, Any]:
    soup = BeautifulSoup(html, "lxml")
    heading = soup.find("div", class_="inline-h3")
    total = None
    if heading:
        match = re.search(r"（(\d+)门）", heading.get_text())
        if match:
            total = int(match.group(1))

    items = []
    for card in soup.find_all("div", class_="ud-pd-md dashed"):
        course_link = card.find("a", href=re.compile(r"^/course/\d+/?$"))
        if course_link is None:
            continue
        href_match = re.search(r"/course/(\d+)", course_link["href"])
        term_node = card.find(
            "span", class_="small grey align-bottom left-pd-sm"
        )
        term = None
        if term_node:
            term = _clean(term_node.get_text()).removeprefix("学期：").strip()

        time_node = card.find("span", class_="localtime")
        excerpt = card.find("p", class_="dark-grey")
        if excerpt:
            for more in excerpt.find_all("a", href=re.compile("#review-")):
                more.extract()
        excerpt_html = excerpt.decode_contents() if excerpt else ""

        upvotes = comment_count = None
        upvote_node = card.find("span", id=re.compile(r"^review-upvote-count-"))
        if upvote_node:
            match = re.search(r"(\d+)", upvote_node.get_text())
            if match:
                upvotes = int(match.group(1))
        comment_node = card.find("span", id=re.compile(r"^review-comment-count-"))
        if comment_node:
            match = re.search(r"(\d+)", comment_node.get_text())
            if match:
                comment_count = int(match.group(1))

        labels = [_clean(label.get_text()) for label in card.find_all("span", class_="label")]
        items.append(
            {
                "course_id": href_match.group(1) if href_match else None,
                "course_title": _clean(course_link.get_text()),
                "url": _absolute(course_link["href"]),
                "term": term,
                "labels": labels,
                "only_visible_to_student": "仅登录学生可见" in labels,
                "created_at": _iso_utc(time_node.get_text()) if time_node else None,
                "excerpt_html": excerpt_html,
                "excerpt_text": _html_to_text(excerpt_html),
                "upvotes": upvotes,
                "comment_count": comment_count,
            }
        )
    return {"total": total, "items": items}


# --------------------------------------------------------------------------- #
# 富文本：公式归一化（对应站点 static/js/review-math.js）
# --------------------------------------------------------------------------- #


def normalize_display_math(html: str) -> str:
    """把跨段落的 ``\\[...\\]`` / ``$$...$$`` 公式压回单个节点。

    站点编辑器会把显示公式拆成多个 ``<p>``，MathJax 无法配对。前端
    ``review-math.js`` 在渲染前做同样的归一化；离线解析时若要把点评
    转成 Markdown/纯文本，也需要先调用本函数。
    """
    html = re.sub(
        r"\\\[(.*?)\\\]",
        lambda match: '<span class="math-display">\\['
        + _flatten_math_body(match.group(1))
        + "\\]</span>",
        html,
        flags=re.S,
    )
    html = re.sub(
        r"\$\$(.*?)\$\$",
        lambda match: '<span class="math-display">$$'
        + _flatten_math_body(match.group(1))
        + "$$</span>",
        html,
        flags=re.S,
    )
    return _convert_bare_bracket(html)


def _flatten_math_body(body: str) -> str:
    body = re.sub(r"<\s*br\s*/?\s*>", "\n", body, flags=re.I)
    body = re.sub(r"</\s*(?:p|div|h[1-6])\s*>", "\n", body, flags=re.I)
    body = re.sub(r"<\s*(?:p|div|h[1-6])[^>]*>", "", body, flags=re.I)
    body = re.sub(r"<[^>]+>", "", body)
    return body.replace("&nbsp;", " ")


def _convert_bare_bracket(html: str) -> str:
    ws = r"(?:\s|&nbsp;)*"

    def block_replace(match: re.Match[str]) -> str:
        body = _flatten_math_body(match.group(1))
        if not re.sub(r"\s| ", "", body):
            return match.group(0)
        return '<span class="math-display">\\[' + body + "\\]</span>"

    html = re.sub(
        r"<(?:p|div)[^>]*>" + ws + r"\[" + ws + r"</(?:p|div)>"
        r"([\s\S]*?)"
        r"<(?:p|div)[^>]*>" + ws + r"\]" + ws + r"</(?:p|div)>",
        block_replace,
        html,
        flags=re.I,
    )

    def br_replace(match: re.Match[str]) -> str:
        body = _flatten_math_body(match.group(2))
        if not re.sub(r"\s| ", "", body):
            return match.group(0)
        return (
            match.group(1)
            + '<span class="math-display">\\['
            + body
            + "\\]</span>"
        )

    pattern = (
        r"(<p[^>]*>|<div[^>]*>|<br\s*/?>|^)"
        + ws
        + r"\["
        + ws
        + r"<br\s*/?>"
        + r"([\s\S]*?)"
        + r"<br\s*/?>"
        + ws
        + r"\]"
        + ws
        + r"(?=</p>|</div>|<br\s*/?>|$)"
    )
    html = re.sub(pattern, br_replace, html, flags=re.I)
    return html


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #


def _build_client(args: argparse.Namespace) -> ICourseClient:
    client = ICourseClient()
    username = args.username or os.environ.get("ICOURSE_USERNAME")
    password = args.password or os.environ.get("ICOURSE_PASSWORD")
    if username and password:
        client.login(username, password)
    return client


def _print_json(value: Any) -> None:
    json.dump(value, sys.stdout, ensure_ascii=False, indent=2)
    sys.stdout.write("\n")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="icourse.club 只读解析器")
    parser.add_argument("--username", help="用户名；也可用 ICOURSE_USERNAME")
    parser.add_argument("--password", help="密码；也可用 ICOURSE_PASSWORD")
    subparsers = parser.add_subparsers(dest="command", required=True)

    login_parser = subparsers.add_parser("login", help="验证登录并输出会话信息")
    login_parser.set_defaults(func=lambda client, _: {
        "logged_in": client.user_id is not None,
        "user_id": client.user_id,
        "session": {
            key: value
            for key, value in (client.session_info() or {}).items()
            if key in {"_user_id", "csrf_token", "_fresh"}
        },
    })

    course_parser = subparsers.add_parser("course", help="解析课程详情与全部点评")
    course_parser.add_argument("course_id")
    course_parser.add_argument("--sort-by", choices=["upvote", "pubtime_desc", "pubtime", "score_desc", "score"])
    course_parser.add_argument("--term", help="如 20251")
    course_parser.add_argument("--rating", type=int, choices=[1, 2, 3, 4, 5])
    course_parser.set_defaults(func=lambda client, args: client.get_course(
        args.course_id, sort_by=args.sort_by, term=args.term, rating=args.rating
    ))

    list_parser = subparsers.add_parser("courses", help="课程列表")
    list_parser.add_argument("--q", default="")
    list_parser.add_argument("--type", dest="course_type")
    list_parser.add_argument("--sort-by", choices=["rating", "popular"])
    list_parser.add_argument("--page", type=int, default=1)
    list_parser.set_defaults(func=lambda client, args: client.list_courses(
        q=args.q, course_type=args.course_type, sort_by=args.sort_by, page=args.page
    ))

    search_parser = subparsers.add_parser("search", help="搜索课程")
    search_parser.add_argument("q")
    search_parser.add_argument("--page", type=int, default=1)
    search_parser.set_defaults(func=lambda client, args: client.search_courses(args.q, page=args.page))

    search_reviews_parser = subparsers.add_parser("search-reviews", help="搜索点评")
    search_reviews_parser.add_argument("q")
    search_reviews_parser.add_argument("--page", type=int, default=1)
    search_reviews_parser.set_defaults(func=lambda client, args: client.search_reviews(args.q, page=args.page))

    latest_parser = subparsers.add_parser("latest", help="最新点评动态")
    latest_parser.add_argument("--page", type=int, default=1)
    latest_parser.add_argument("--q", default="")
    latest_parser.set_defaults(func=lambda client, args: client.latest_reviews(page=args.page, q=args.q))

    comments_parser = subparsers.add_parser("comments", help="获取单条点评的评论")
    comments_parser.add_argument("review_id")
    comments_parser.set_defaults(func=lambda client, args: client.get_comments(args.review_id))

    user_parser = subparsers.add_parser("user-reviews", help="用户点评列表")
    user_parser.add_argument("user_id")
    user_parser.add_argument("--page", type=int, default=1)
    user_parser.set_defaults(func=lambda client, args: client.user_reviews(args.user_id, page=args.page))

    args = parser.parse_args(list(argv) if argv is not None else None)
    client = _build_client(args)
    try:
        result = args.func(client, args)
    except (ICourseError, requests.RequestException) as exc:
        sys.stderr.write(f"错误：{exc}\n")
        return 1
    _print_json(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
