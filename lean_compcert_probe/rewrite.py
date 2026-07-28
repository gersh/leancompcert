from __future__ import annotations

import re
from dataclasses import dataclass


@dataclass(frozen=True)
class RewriteResult:
    text: str
    applied: tuple[str, ...]


def mechanical_rewrite(source: str) -> RewriteResult:
    """Apply deliberately conservative rewrites to a copy of generated C."""
    text = source
    applied: list[str] = []

    replacements = (
        (
            "remove always_inline attribute",
            re.compile(r"__attribute__\s*\(\(\s*always_inline\s*\)\)"),
            "",
        ),
        (
            "remove unused attribute",
            re.compile(r"__attribute__\s*\(\(\s*unused\s*\)\)"),
            "",
        ),
        (
            "replace force-inline macro",
            re.compile(r"\bLEAN_ALWAYS_INLINE\b"),
            "inline",
        ),
    )
    for name, pattern, replacement in replacements:
        text, count = pattern.subn(replacement, text)
        if count:
            applied.append(name)

    # Lean's C emitter initializes the flexible m_data[] member directly.
    # CompCert rejects that GCC extension.  The anonymous fixed-size struct has
    # the same field order and uses sizeof on the exact C literal, including its
    # terminating NUL byte.
    static_string = re.compile(
        r"static\s+const\s+lean_string_object\s+([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*=\s*(\{[^\n;]*?\.m_data\s*=\s*(\"(?:\\.|[^\"\\])*\")[^\n;]*\})\s*;"
    )

    def replace_static_string(match: re.Match[str]) -> str:
        name = match.group(1)
        initializer = match.group(2)
        literal = match.group(3)
        return (
            "static const struct { lean_object m_header; size_t m_size; "
            "size_t m_capacity; size_t m_length; "
            f"char m_data[sizeof({literal})]; }} {name} = {initializer};"
        )

    text, count = static_string.subn(replace_static_string, text)
    if count:
        applied.append("materialize static string flexible array")

    static_ctor = re.compile(
        r"static\s+const\s+lean_ctor_object\s+([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*=\s*(\{[^\n;]*?\.m_objs\s*=\s*\{([^\n{}]*)\}[^\n;]*\})\s*;"
    )

    def count_top_level_items(value: str) -> int:
        if not value.strip():
            return 0
        depth = 0
        items = 1
        escaped = False
        quoted = False
        for character in value:
            if quoted:
                if escaped:
                    escaped = False
                elif character == "\\":
                    escaped = True
                elif character == '"':
                    quoted = False
            elif character == '"':
                quoted = True
            elif character == "(":
                depth += 1
            elif character == ")":
                depth = max(0, depth - 1)
            elif character == "," and depth == 0:
                items += 1
        return items

    def replace_static_ctor(match: re.Match[str]) -> str:
        name = match.group(1)
        initializer = match.group(2)
        fields = max(1, count_top_level_items(match.group(3)))
        return (
            "static const struct { lean_object m_header; "
            f"lean_object *m_objs[{fields}]; }} {name} = {initializer};"
        )

    text, count = static_ctor.subn(replace_static_ctor, text)
    if count:
        applied.append("materialize static constructor flexible array")

    # Static closures use the same flexible-array initialization extension.
    # For captured objects, materialize the exact array length.  For a
    # zero-capture closure, omit the flexible member and its empty initializer;
    # normal struct tail padding preserves sizeof(lean_closure_object).
    static_closure = re.compile(
        r"static\s+const\s+lean_closure_object\s+([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*=\s*(\{[^\n;]*?\.m_objs\s*=\s*\{([^\n{}]*)\}[^\n;]*\})\s*;"
    )

    def replace_static_closure(match: re.Match[str]) -> str:
        name = match.group(1)
        initializer = match.group(2)
        fields = count_top_level_items(match.group(3))
        prefix = (
            "static const struct { lean_object m_header; void *m_fun; "
            "uint16_t m_arity; uint16_t m_num_fixed;"
        )
        if fields == 0:
            initializer = re.sub(
                r",?\s*\.m_objs\s*=\s*\{\s*\}", "", initializer
            )
            return f"{prefix} }} {name} = {initializer};"
        return (
            f"{prefix} lean_object *m_objs[{fields}]; }} "
            f"{name} = {initializer};"
        )

    text, count = static_closure.subn(replace_static_closure, text)
    if count:
        applied.append("materialize static closure flexible array")

    def rewrite_static_array(
        current: str, c_type: str, element_type: str, label: str
    ) -> tuple[str, int]:
        pattern = re.compile(
            rf"static\s+const\s+{c_type}\s+([A-Za-z_][A-Za-z0-9_]*)"
            r"\s*=\s*(\{[^\n;]*?\.m_data\s*=\s*\{([^\n{}]*)\}[^\n;]*\})\s*;"
        )

        def replace(match: re.Match[str]) -> str:
            name = match.group(1)
            initializer = match.group(2)
            fields = count_top_level_items(match.group(3))
            prefix = (
                "static const struct { lean_object m_header; "
                "size_t m_size; size_t m_capacity;"
            )
            if fields == 0:
                initializer = re.sub(
                    r",?\s*\.m_data\s*=\s*\{\s*\}", "", initializer
                )
                return f"{prefix} }} {name} = {initializer};"
            return (
                f"{prefix} {element_type} m_data[{fields}]; }} "
                f"{name} = {initializer};"
            )

        return pattern.subn(replace, current)

    text, count = rewrite_static_array(
        text, "lean_array_object", "lean_object *", "object"
    )
    if count:
        applied.append("materialize static object-array flexible array")
    text, count = rewrite_static_array(
        text, "lean_sarray_object", "uint8_t", "scalar"
    )
    if count:
        applied.append("materialize static scalar-array flexible array")
    return RewriteResult(text=text, applied=tuple(applied))
