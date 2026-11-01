"""The design system of the site as data with decided theorems, generated
into `Presentation.lex.tex` (the declarations below are appended to the
presentation's) and emitted as CSS custom properties by `site.py`.

- `Token`: a colour role with its sRGB value in the light and in the dark
  theme (three 8-bit channels each) and the relative luminance of each,
  scaled by 10^10 (the WCAG 2.2 definition: each channel linearized through
  `srgbLinear`, the 256 values of the sRGB transfer function scaled by 10^6,
  then weighted 2126, 7152, 722 over 10^4). The kernel decides that every
  stored luminance is the one computed from the channels
  (`tokenLuminancesComputed`), so the contrast theorems below rest on the
  colours, not on a number typed beside them.
- `ContrastPair`: a foreground on a background with its use (`text`,
  `large-text`, `ui`) and the minimum ratio times ten (45 for text, 30 for
  large text and for user-interface components and graphical objects,
  WCAG 2.2 success criteria 1.4.3 and 1.4.11). The kernel decides
  `everyPairMeetsContrastLight` and `everyPairMeetsContrastDark` in integer
  arithmetic: with L the luminances times 10^10 and 0.05 as 5 * 10^8,
  minimum * (darker + 5*10^8) <= 10 * (lighter + 5*10^8).
- `TypeStep`, `SpaceStep`, `Motion`: the type scale (rem times 100, line
  height times 100), the spacing scale (CSS pixels), the motion durations
  with their reduced-motion variant (milliseconds); decided: both scales
  strictly increase, body text is at least 1rem, the smallest target is at
  least 24px (WCAG 2.2 target size, 2.5.8), every reduced duration is 0
  (2.3.3 animation from interactions) and every animation ends within 5 s
  (2.2.2 pause, stop, hide needs no control below that).
- `Landing`: the one screen that tells the story: the question, what is
  proved, what is open, and the vantages as entry points; decided: its
  obligation is the presentation's open obligation and its entries are
  exactly the journeys.
"""

from .semantic import (BOOL, NAT, STR, add, b, ble, call, definition, eq_string, field_of_each, holds, if_, list_t, lst,
                       match_list, n, named, proj, record, s, strings, structure, var)

# 0.05 in the luminance scale (10^10)
OFFSET = 500_000_000


def _linear(c):
    v = c / 255
    return v / 12.92 if v <= 0.04045 else ((v + 0.055) / 1.055) ** 2.4


# The sRGB transfer function on the 256 channel values, times 10^6.
SRGB_LINEAR = [round(_linear(i) * 1_000_000) for i in range(256)]


def channels(hex_colour):
    return [int(hex_colour[i:i + 2], 16) for i in (1, 3, 5)]


def luminance(hex_colour):
    """Relative luminance times 10^10, exactly as the kernel computes it."""
    r, g, bl = channels(hex_colour)
    return 2126 * SRGB_LINEAR[r] + 7152 * SRGB_LINEAR[g] + 722 * SRGB_LINEAR[bl]


def ratio(a, c):
    la, lc = luminance(a), luminance(c)
    return (max(la, lc) + OFFSET) / (min(la, lc) + OFFSET)


def meets(a, c, minimum):
    la, lc = sorted((luminance(a), luminance(c)))
    return minimum * (la + OFFSET) <= 10 * (lc + OFFSET)


# The colour roles. `css` is the custom property the stylesheet uses; the
# names are the ones every panel and visualization of the site reads.
TOKENS = [
    {"id": "bg", "role": "surface", "light": "#f6f3ec", "dark": "#101217", "statement": "The page: warm paper by day, near-black by night."},
    {"id": "panel", "role": "surface", "light": "#fdfcf9", "dark": "#181b21", "statement": "Cards, panels and the banner."},
    {"id": "soft", "role": "surface", "light": "#ece7dc", "dark": "#22262e", "statement": "Hover, selection and table heads."},
    {"id": "line", "role": "decoration", "light": "#ddd6c8", "dark": "#2c3039", "statement": "Hairlines between regions; never the only cue."},
    {"id": "line-strong", "role": "ui", "light": "#8b8677", "dark": "#6f7682", "statement": "The boundary of a field or a control."},
    {"id": "ink", "role": "text", "light": "#16181d", "dark": "#ece8df", "statement": "Body text."},
    {"id": "muted", "role": "text", "light": "#585c64", "dark": "#a4a9b2", "statement": "Secondary text: captions, metadata, Lean names."},
    {"id": "accent", "role": "graphic", "light": "#a06600", "dark": "#e8a93a", "statement": "Amber: the center column, the current step, the one highlight."},
    {"id": "accent-text", "role": "text", "light": "#855500", "dark": "#ebb557", "statement": "Amber as text."},
    {"id": "accent-ink", "role": "text", "light": "#ffffff", "dark": "#16181d", "statement": "Text on an amber fill."},
    {"id": "accent-soft", "role": "surface", "light": "#f7e7c4", "dark": "#3a2d12", "statement": "A quiet amber wash behind the goal of a step."},
    {"id": "link", "role": "text", "light": "#1b5a86", "dark": "#8cc2ea", "statement": "Links."},
    {"id": "focus", "role": "ui", "light": "#1b5a86", "dark": "#8cc2ea", "statement": "The one focus ring."},
    {"id": "cell", "role": "graphic", "light": "#2a2d33", "dark": "#d9d4c9", "statement": "A black cell of Rule 30 (light on the night page)."},
    {"id": "open", "role": "text", "light": "#7a5104", "dark": "#e8b04a", "statement": "An open claim."},
    {"id": "open-bg", "role": "surface", "light": "#fbefd3", "dark": "#3a2e12", "statement": "Behind an open mark."},
    {"id": "proved", "role": "text", "light": "#22663e", "dark": "#72d09a", "statement": "A proved claim."},
    {"id": "proved-bg", "role": "surface", "light": "#ddf1e3", "dark": "#163323", "statement": "Behind a proved mark."},
    {"id": "refuted", "role": "text", "light": "#a3302a", "dark": "#f08c82", "statement": "A refuted route."},
    {"id": "refuted-bg", "role": "surface", "light": "#f9dfdc", "dark": "#3f1f1c", "statement": "Behind a refuted mark."},
    {"id": "retired", "role": "text", "light": "#575b61", "dark": "#a4a9b2", "statement": "A retired claim."},
    {"id": "retired-bg", "role": "surface", "light": "#e8e7e4", "dark": "#2a2d33", "statement": "Behind a retired mark."},
]

MINIMUM = {"text": 45, "large-text": 30, "ui": 30}

# Every pair the stylesheet puts one token on another, with its use.
PAIRS = [(fg, bg_, "text") for fg in ("ink", "muted", "link") for bg_ in ("bg", "panel", "soft")] + [
    ("accent-text", "bg", "text"), ("accent-text", "panel", "text"), ("accent-ink", "accent", "text"), ("ink", "accent-soft", "text"),
    ("muted", "accent-soft", "text"),
    ("open", "open-bg", "text"), ("open", "panel", "text"), ("proved", "proved-bg", "text"), ("proved", "panel", "text"),
    ("refuted", "refuted-bg", "text"), ("refuted", "panel", "text"), ("retired", "retired-bg", "text"), ("retired", "panel", "text"),
    ("ink", "open-bg", "text"),
    ("focus", "bg", "ui"), ("focus", "panel", "ui"), ("line-strong", "bg", "ui"), ("line-strong", "panel", "ui"),
    ("accent", "bg", "ui"), ("accent", "panel", "ui"), ("cell", "bg", "ui"), ("cell", "panel", "ui"),
]
PAIRS = [{"foreground": f, "background": g, "use": u, "minimum": MINIMUM[u]} for f, g, u in PAIRS]

FONTS = {
    "serif": '"Iowan Old Style", "Charter", "Palatino Linotype", Palatino, "Book Antiqua", Georgia, serif',
    "sans": 'system-ui, -apple-system, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif',
    "mono": 'ui-monospace, "SF Mono", SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace',
}

# rem times 100, line height times 100
TYPE_SCALE = [
    {"id": "xs", "size": 78, "leading": 140, "family": "sans", "use": "Badges, kappa labels."},
    {"id": "sm", "size": 88, "leading": 150, "family": "sans", "use": "Captions, metadata, Lean names."},
    {"id": "base", "size": 100, "leading": 160, "family": "sans", "use": "Body text."},
    {"id": "md", "size": 115, "leading": 150, "family": "serif", "use": "Lede and card titles."},
    {"id": "lg", "size": 140, "leading": 125, "family": "serif", "use": "Panel titles."},
    {"id": "xl", "size": 185, "leading": 115, "family": "serif", "use": "Step titles."},
    {"id": "display", "size": 280, "leading": 105, "family": "serif", "use": "The question on the landing."},
]

# CSS pixels
SPACING = [
    {"id": "hair", "size": 2}, {"id": "xxs", "size": 4}, {"id": "xs", "size": 8}, {"id": "sm", "size": 12}, {"id": "md", "size": 16},
    {"id": "target", "size": 24}, {"id": "lg", "size": 32}, {"id": "xl", "size": 48}, {"id": "xxl", "size": 72}, {"id": "huge", "size": 112},
]
TARGET_MINIMUM = 24
BODY_MINIMUM = 100
PAUSE_THRESHOLD = 5000

# milliseconds; `reduced` is the duration under prefers-reduced-motion
MOTION = [
    {"id": "quick", "duration": 140, "reduced": 0, "easing": "cubic-bezier(0.2, 0, 0, 1)", "use": "Hover and press feedback."},
    {"id": "step", "duration": 280, "reduced": 0, "easing": "cubic-bezier(0.2, 0, 0, 1)", "use": "A step entering after the previous one."},
    {"id": "card", "duration": 220, "reduced": 0, "easing": "cubic-bezier(0.3, 0, 0, 1)", "use": "An evidence card opening in place."},
    {"id": "reveal", "duration": 2600, "reduced": 0, "easing": "linear", "use": "The triangle drawn row by row on the landing; it then rests."},
]

LANDING = {
    "question": "Does the center column of Rule 30 ever repeat?",
    "proved": "Kernel-checked arrows reduce the question to one open statement about the interior of the triangle.",
    "open": "That statement, aperiodic-compensation, is open: nobody has proved it, and nothing on this site claims a proof of it.",
    "obligation": "aperiodic-compensation",
    "entries": ["first-visit", "mathematics", "prize-review", "research-session", "reading", "stdlib-feedback"],
}


def css_name(token_id):
    return "--" + token_id


def problems(journeys, obligation):
    """What the kernel decides about the design system, checked first in
    Python so a failure names the token or the pair."""
    ids = [t["id"] for t in TOKENS]
    out = []
    if len(set(ids)) != len(ids):
        out.append("tokens: ids are not distinct")
    by = {t["id"]: t for t in TOKENS}
    for p in PAIRS:
        for side in ("foreground", "background"):
            if p[side] not in by:
                out.append(f"pair {p['foreground']} on {p['background']}: {p[side]} is not a token")
        if p["minimum"] != MINIMUM.get(p["use"]):
            out.append(f"pair {p['foreground']} on {p['background']}: minimum {p['minimum']} is not WCAG's for {p['use']}")
        if p["foreground"] in by and p["background"] in by:
            for mode in ("light", "dark"):
                f, g = by[p["foreground"]][mode], by[p["background"]][mode]
                if not meets(f, g, p["minimum"]):
                    out.append(f"pair {p['foreground']} on {p['background']} ({mode}): {ratio(f, g):.2f}:1 is below {p['minimum'] / 10}:1")
    for t in TOKENS:
        if t["role"] == "text" and not any(p["foreground"] == t["id"] for p in PAIRS):
            out.append(f"token {t['id']}: a text colour on no declared background")
    for name, rows in (("type scale", TYPE_SCALE), ("spacing", SPACING)):
        sizes = [r["size"] for r in rows]
        if any(a >= c for a, c in zip(sizes, sizes[1:])):
            out.append(f"{name}: not strictly increasing")
    if next(r["size"] for r in TYPE_SCALE if r["id"] == "base") < BODY_MINIMUM:
        out.append("type scale: body text below 1rem")
    if next(r["size"] for r in SPACING if r["id"] == "target") < TARGET_MINIMUM:
        out.append("spacing: the target size is below 24px")
    for m in MOTION:
        if m["reduced"] != 0:
            out.append(f"motion {m['id']}: the reduced duration is not 0")
        if m["duration"] > PAUSE_THRESHOLD:
            out.append(f"motion {m['id']}: longer than 5 s without a control")
    if LANDING["obligation"] != obligation:
        out.append("landing: its obligation is not the presentation's")
    if sorted(LANDING["entries"]) != sorted(j["id"] for j in journeys):
        out.append("landing: its entries are not exactly the journeys")
    return out


def css(selector_light=":root", selector_dark=':root[data-theme="dark"]'):
    """The tokens as CSS custom properties: the light theme on :root, the
    dark theme under prefers-color-scheme (unless the reader chose light) and
    under an explicit choice; the scales and motion as properties, the
    reduced-motion variant under prefers-reduced-motion."""
    def block(mode):
        return " ".join(f"{css_name(t['id'])}: {t[mode]};" for t in TOKENS)
    scale = " ".join(f"--text-{r['id']}: {r['size'] / 100:g}rem; --leading-{r['id']}: {r['leading'] / 100:g};" for r in TYPE_SCALE)
    space = " ".join(f"--space-{r['id']}: {r['size']}px;" for r in SPACING)
    motion = " ".join(f"--motion-{m['id']}: {m['duration']}ms; --ease-{m['id']}: {m['easing']};" for m in MOTION)
    reduced = " ".join(f"--motion-{m['id']}: {m['reduced']}ms;" for m in MOTION)
    fonts = " ".join(f"--{k}: {v};" for k, v in FONTS.items())
    return ("/* generated by tools/r30/designmodel.py from Presentation.lex.tex (tokens, typeScale, spacing, motion); "
            "the kernel decides every contrast pair below in both themes */\n"
            f"{selector_light} {{ color-scheme: light; {block('light')}\n  {fonts}\n  {scale}\n  {space}\n  {motion} }}\n"
            f"@media (prefers-color-scheme: dark) {{ :root:not([data-theme=\"light\"]) {{ color-scheme: dark; {block('dark')} }} }}\n"
            f"{selector_dark} {{ color-scheme: dark; {block('dark')} }}\n"
            f"@media (prefers-reduced-motion: reduce) {{ :root {{ {reduced} }} }}\n")


def view_data():
    """The design system as the site reads it (the design panel)."""
    return {"tokens": [dict(t, luminance={m: luminance(t[m]) for m in ("light", "dark")}) for t in TOKENS],
            "pairs": [dict(p, ratio={m: round(ratio(next(t[m] for t in TOKENS if t["id"] == p["foreground"]),
                                                     next(t[m] for t in TOKENS if t["id"] == p["background"])), 2)
                                     for m in ("light", "dark")}) for p in PAIRS],
            "typeScale": TYPE_SCALE, "spacing": SPACING, "motion": MOTION, "fonts": FONTS, "landing": LANDING}


# ---- the declarations appended to Presentation.lex.tex ----

def _mul(a, c):
    return {"kind": "primitive", "operation": "multiply", "result": NAT, "arguments": [a, c]}


def _sub(a, c):
    return {"kind": "primitive", "operation": "subtract", "result": NAT, "arguments": [a, c]}


def _all_nat(name, element, condition, extra=()):
    """`name xs ...`: `condition` (over `head`) holds of every element."""
    params = [("xs", list_t(element))] + list(extra)
    return definition(name, BOOL, match_list(var("xs"), b(True), "head", "tail",
                                             if_(condition, call(name, var("tail"), *[var(q) for q, _ in extra]), b(False))),
                      parameters=params, recursive="xs")


def declarations():
    tk_t, cp_t, ts_t, sp_t, mo_t, la_t = (named(x) for x in ("Token", "ContrastPair", "TypeStep", "SpaceStep", "Motion", "Landing"))
    rgb = lambda prefix, h: dict(zip((prefix + "Red", prefix + "Green", prefix + "Blue"), (n(c) for c in channels(h))))
    empty_token = record("Token", id=s(""), role=s(""), lightRed=n(0), lightGreen=n(0), lightBlue=n(0), darkRed=n(0), darkGreen=n(0),
                         darkBlue=n(0), lightLuminance=n(0), darkLuminance=n(0))

    def lum_of(t, prefix):
        return call("luminance", proj(t, prefix + "Red"), proj(t, prefix + "Green"), proj(t, prefix + "Blue"))

    def pair_meets(mode):
        field = mode + "Luminance"
        return call("meetsContrast", proj(call("tokenOf", proj(var("head"), "foreground"), var("ts")), field),
                    proj(call("tokenOf", proj(var("head"), "background"), var("ts")), field), proj(var("head"), "minimum"))

    return [
        structure("Token", [("id", STR), ("role", STR), ("lightRed", NAT), ("lightGreen", NAT), ("lightBlue", NAT), ("darkRed", NAT),
                            ("darkGreen", NAT), ("darkBlue", NAT), ("lightLuminance", NAT), ("darkLuminance", NAT)]),
        structure("ContrastPair", [("foreground", STR), ("background", STR), ("purpose", STR), ("minimum", NAT)]),
        structure("TypeStep", [("id", STR), ("size", NAT), ("leading", NAT), ("family", STR)]),
        structure("SpaceStep", [("id", STR), ("size", NAT)]),
        structure("Motion", [("id", STR), ("duration", NAT), ("reduced", NAT), ("easing", STR)]),
        structure("Landing", [("question", STR), ("provedStatement", STR), ("openStatement", STR), ("obligation", STR), ("entries", list_t(STR))]),
        definition("srgbLinear", list_t(NAT), lst([n(v) for v in SRGB_LINEAR], NAT)),
        definition("tokens", list_t(tk_t), lst([
            record("Token", id=s(t["id"]), role=s(t["role"]), **rgb("light", t["light"]), **rgb("dark", t["dark"]),
                   lightLuminance=n(luminance(t["light"])), darkLuminance=n(luminance(t["dark"]))) for t in TOKENS], tk_t)),
        definition("contrastPairs", list_t(cp_t), lst([
            record("ContrastPair", foreground=s(p["foreground"]), background=s(p["background"]), purpose=s(p["use"]), minimum=n(p["minimum"]))
            for p in PAIRS], cp_t)),
        definition("typeScale", list_t(ts_t), lst([
            record("TypeStep", id=s(r["id"]), size=n(r["size"]), leading=n(r["leading"]), family=s(r["family"])) for r in TYPE_SCALE], ts_t)),
        definition("spacing", list_t(sp_t), lst([record("SpaceStep", id=s(r["id"]), size=n(r["size"])) for r in SPACING], sp_t)),
        definition("motion", list_t(mo_t), lst([
            record("Motion", id=s(m["id"]), duration=n(m["duration"]), reduced=n(m["reduced"]), easing=s(m["easing"])) for m in MOTION], mo_t)),
        definition("landing", la_t, record("Landing", question=s(LANDING["question"]), provedStatement=s(LANDING["proved"]), openStatement=s(LANDING["open"]),
                                           obligation=s(LANDING["obligation"]), entries=strings(LANDING["entries"]))),
        # the WCAG 2.2 relative luminance, times 10^10, from 8-bit channels
        definition("nthNat", NAT,
                   match_list(var("xs"), n(0), "head", "tail",
                              if_({"kind": "beq", "left": var("k"), "right": n(0)}, var("head"), call("nthNat", var("tail"), _sub(var("k"), n(1))))),
                   parameters=[("xs", list_t(NAT)), ("k", NAT)], recursive="xs"),
        definition("luminance", NAT,
                   add(add(_mul(n(2126), call("nthNat", call("srgbLinear"), var("r"))), _mul(n(7152), call("nthNat", call("srgbLinear"), var("g")))),
                       _mul(n(722), call("nthNat", call("srgbLinear"), var("bl")))),
                   parameters=[("r", NAT), ("g", NAT), ("bl", NAT)]),
        # (lighter + 0.05) / (darker + 0.05) >= minimum / 10, cross-multiplied
        definition("meetsContrast", BOOL,
                   if_(ble(var("x"), var("y")),
                       ble(_mul(var("minimum"), add(var("x"), n(OFFSET))), _mul(n(10), add(var("y"), n(OFFSET)))),
                       ble(_mul(var("minimum"), add(var("y"), n(OFFSET))), _mul(n(10), add(var("x"), n(OFFSET))))),
                   parameters=[("x", NAT), ("y", NAT), ("minimum", NAT)]),
        definition("tokenOf", tk_t,
                   match_list(var("xs"), empty_token, "head", "tail",
                              if_(eq_string(var("key"), proj(var("head"), "id")), var("head"), call("tokenOf", var("key"), var("tail")))),
                   parameters=[("key", STR), ("xs", list_t(tk_t))], recursive="xs"),
        _all_nat("luminancesComputed", tk_t,
                 if_({"kind": "beq", "left": proj(var("head"), "lightLuminance"), "right": lum_of(var("head"), "light")},
                     {"kind": "beq", "left": proj(var("head"), "darkLuminance"), "right": lum_of(var("head"), "dark")}, b(False))),
        _all_nat("pairsMeetLight", cp_t, pair_meets("light"), extra=[("ts", list_t(tk_t))]),
        _all_nat("pairsMeetDark", cp_t, pair_meets("dark"), extra=[("ts", list_t(tk_t))]),
        # the minimum of a pair is WCAG's for its use
        definition("wcagMinimum", NAT,
                   if_(eq_string(var("purpose"), s("text")), n(MINIMUM["text"]), n(MINIMUM["ui"])),
                   parameters=[("purpose", STR)]),
        _all_nat("pairMinimumsWcag", cp_t,
                 if_(call("memberString", proj(var("head"), "purpose"), strings(sorted(MINIMUM))),
                     {"kind": "beq", "left": proj(var("head"), "minimum"), "right": call("wcagMinimum", proj(var("head"), "purpose"))}, b(False))),
        field_of_each("tokenIds", tk_t, "id"),
        field_of_each("pairForegrounds", cp_t, "foreground"),
        field_of_each("pairBackgrounds", cp_t, "background"),
        field_of_each("typeSizes", ts_t, "size", result=NAT),
        field_of_each("spaceSizes", sp_t, "size", result=NAT),
        definition("strictlyIncreasing", BOOL,
                   match_list(var("xs"), b(True), "head", "tail",
                              if_({"kind": "blt", "left": var("previous"), "right": var("head")},
                                  call("strictlyIncreasing", var("tail"), var("head")), b(False))),
                   parameters=[("xs", list_t(NAT)), ("previous", NAT)], recursive="xs"),
        definition("textTokenIds", list_t(STR),
                   match_list(var("xs"), {"kind": "nil", "element": STR}, "head", "tail",
                              if_(eq_string(proj(var("head"), "role"), s("text")),
                                  {"kind": "cons", "head": proj(var("head"), "id"), "tail": call("textTokenIds", var("tail"))},
                                  call("textTokenIds", var("tail")))),
                   parameters=[("xs", list_t(tk_t))], recursive="xs"),
        definition("typeSize", NAT,
                   match_list(var("xs"), n(0), "head", "tail",
                              if_(eq_string(var("key"), proj(var("head"), "id")), proj(var("head"), "size"), call("typeSize", var("key"), var("tail")))),
                   parameters=[("key", STR), ("xs", list_t(ts_t))], recursive="xs"),
        definition("spaceSize", NAT,
                   match_list(var("xs"), n(0), "head", "tail",
                              if_(eq_string(var("key"), proj(var("head"), "id")), proj(var("head"), "size"), call("spaceSize", var("key"), var("tail")))),
                   parameters=[("key", STR), ("xs", list_t(sp_t))], recursive="xs"),
        _all_nat("motionReducedToZero", mo_t, {"kind": "beq", "left": proj(var("head"), "reduced"), "right": n(0)}),
        _all_nat("motionWithinPause", mo_t, ble(proj(var("head"), "duration"), n(PAUSE_THRESHOLD))),
        holds("tokenIdsDistinct", call("distinctStrings", call("tokenIds", call("tokens")))),
        holds("tokenLuminancesComputed", call("luminancesComputed", call("tokens"))),
        holds("pairsNameTokens", call("allMembers", call("appendStrings", call("pairForegrounds", call("contrastPairs")),
                                                         call("pairBackgrounds", call("contrastPairs"))), call("tokenIds", call("tokens")))),
        holds("everyTextTokenOnABackground", call("allMembers", call("textTokenIds", call("tokens")), call("pairForegrounds", call("contrastPairs")))),
        holds("pairMinimumsAreWcag", call("pairMinimumsWcag", call("contrastPairs"))),
        holds("everyPairMeetsContrastLight", call("pairsMeetLight", call("contrastPairs"), call("tokens"))),
        holds("everyPairMeetsContrastDark", call("pairsMeetDark", call("contrastPairs"), call("tokens"))),
        holds("typeScaleIncreasing", call("strictlyIncreasing", call("typeSizes", call("typeScale")), n(0))),
        holds("spacingIncreasing", call("strictlyIncreasing", call("spaceSizes", call("spacing")), n(0))),
        holds("bodyTextAtLeastOneRem", ble(n(BODY_MINIMUM), call("typeSize", s("base"), call("typeScale")))),
        holds("targetAtLeast24px", ble(n(TARGET_MINIMUM), call("spaceSize", s("target"), call("spacing")))),
        holds("reducedMotionIsInstant", call("motionReducedToZero", call("motion"))),
        holds("motionEndsWithinFiveSeconds", call("motionWithinPause", call("motion"))),
        holds("landingNamesTheObligation", eq_string(proj(call("landing"), "obligation"), call("obligation"))),
        holds("landingEntersEveryJourney", call("sameMembers", proj(call("landing"), "entries"), call("journeyIds", call("journeys")))),
    ]


THEOREMS = ["tokenIdsDistinct", "tokenLuminancesComputed", "pairsNameTokens", "everyTextTokenOnABackground", "pairMinimumsAreWcag",
            "everyPairMeetsContrastLight", "everyPairMeetsContrastDark", "typeScaleIncreasing", "spacingIncreasing",
            "bodyTextAtLeastOneRem", "targetAtLeast24px", "reducedMotionIsInstant", "motionEndsWithinFiveSeconds",
            "landingNamesTheObligation", "landingEntersEveryJourney"]
