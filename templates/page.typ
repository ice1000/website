// This is important for typst-book to produce a responsive layout
// and multiple targets.
#import "@preview/shiroa:0.1.2": get-page-width, target, is-web-target, is-pdf-target

#let page-width = get-page-width()
#let is-pdf-target = is-pdf-target()
#let is-web-target = is-web-target()

// todo: move theme style parser to another lib file
#let theme-target = if target.contains("-") { target.split("-").at(1) } else { "light" }
#let theme-style = toml("theme-style.toml").at(theme-target)

#let is-dark-theme = theme-style.at("color-scheme") == "dark"
#let is-light-theme = not is-dark-theme

#let main-color = rgb(theme-style.at("main-color"))
#let dash-color = rgb(theme-style.at("dash-color"))

// Copied from touying
#let markup-text(it, mode: "typ", indent: 0) = {
  assert(mode == "typ" or mode == "md", message: "mode must be 'typ' or 'md'")
  let indent-markup-text = markup-text.with(mode: mode, indent: indent + 2)
  let markup-text = markup-text.with(mode: mode, indent: indent)
  if type(it) == str {
    it
  } else if type(it) == content {
    if it.func() == raw {
      if it.block {
        "\n" + indent * " " + "```" + it.lang + it
          .text
          .split("\n")
          .map(l => "\n" + indent * " " + l)
          .sum(default: "") + "\n" + indent * " " + "```"
      } else {
        "`" + it.text + "`"
      }
    } else if it == [ ] {
      " "
    } else if it.func() == enum.item {
      "\n" + indent * " " + "+ " + indent-markup-text(it.body)
    } else if it.func() == list.item {
      "\n" + indent * " " + "- " + indent-markup-text(it.body)
    } else if it.func() == terms.item {
      "\n" + indent * " " + "/ " + markup-text(it.term) + ": " + indent-markup-text(it.description)
    } else if it.func() == linebreak {
      "\n" + indent * " "
    } else if it.func() == parbreak {
      "\n\n" + indent * " "
    } else if it.func() == strong {
      if mode == "md" {
        "**" + markup-text(it.body) + "**"
      } else {
        "*" + markup-text(it.body) + "*"
      }
    } else if it.func() == emph {
      if mode == "md" {
        "*" + markup-text(it.body) + "*"
      } else {
        "_" + markup-text(it.body) + "_"
      }
    } else if it.func() == link and type(it.dest) == str {
      if mode == "md" {
        "[" + markup-text(it.body) + "](" + it.dest + ")"
      } else {
        "#link(\"" + it.dest + "\")[" + markup-text(it.body) + "]"
      }
    } else if it.func() == heading {
      if mode == "md" {
        it.depth * "#" + " " + markup-text(it.body) + "\n"
      } else {
        it.depth * "=" + " " + markup-text(it.body) + "\n"
      }
    } else if it.has("children") {
      it.children.map(markup-text).join()
    } else if it.has("body") {
      markup-text(it.body)
    } else if it.has("text") {
      if type(it.text) == str {
        it.text
      } else {
        markup-text(it.text)
      }
    } else if it.func() == smartquote {
      if it.double {
        "\""
      } else {
        "'"
      }
    } else {
      ""
    }
  } else {
    repr(it)
  }
}

#let main-font = (
  "Charter",
  "Source Han Serif SC",
  "Source Han Serif TC",
  // typst-book's embedded font
  "Linux Libertine",
)

#let code-font = (
  "BlexMono Nerd Font Mono",
  // typst-book's embedded font
  "DejaVu Sans Mono",
)

// todo: move code theme parser to another lib file
#let code-theme-file = theme-style.at("code-theme")

#let code-extra-colors = if code-theme-file.len() > 0 {
  let data = xml(theme-style.at("code-theme")).first()

  let find-child(elem, tag) = {
    elem.children.find(e => "tag" in e and e.tag == tag)
  }

  let find-kv(elem, key, tag) = {
    let idx = elem.children.position(e => "tag" in e and e.tag == "key" and e.children.first() == key)
    elem.children.slice(idx).find(e => "tag" in e and e.tag == tag)
  }

  let plist-dict = find-child(data, "dict")
  let plist-array = find-child(plist-dict, "array")
  let theme-setting = find-child(plist-array, "dict")
  let theme-setting-items = find-kv(theme-setting, "settings", "dict")
  let background-setting = find-kv(theme-setting-items, "background", "string")
  let foreground-setting = find-kv(theme-setting-items, "foreground", "string")
  (
    bg: rgb(background-setting.children.first()),
    fg: rgb(foreground-setting.children.first()),
  )
} else {
  (
    bg: rgb(239, 241, 243),
    fg: none,
  )
}

#let make-unique-label(it, disambiguator: 1) = label({
  let k = markup-text(it).trim()
  if disambiguator > 1 {
    k + "_d" + str(disambiguator)
  } else {
    k
  }
})

#let heading-reference(it, d: 1) = make-unique-label(it.body, disambiguator: d)

// The project function defines how your document looks.
// It takes your content and some metadata and formats it.
// Go ahead and customize it to your liking!
#let project(title: "Typst Book", authors: (), show-title: false, body) = {

  // set basic document metadata
  set document(author: authors.map(a => a.name), title: title) if not is-pdf-target

  // set web/pdf page properties
  set page(
    numbering: none, 
    number-align: center,
    width: page-width,
  )

  // remove margins for web target
  set page(
    margin: (
      // reserved beautiful top margin
      top: 20pt,
      // reserved for our heading style.
      // If you apply a different heading style, you may remove it.
      left: 20pt,
      // Typst is setting the page's bottom to the baseline of the last line of text. So bad :(.
      bottom: 0.5em,
      // remove rest margins.
      rest: 0pt,
    ),
    // for a website, we don't need pagination.
    height: auto,
  ) if is-web-target;

  // set text style
  set text(font: main-font, size: 16pt, fill: main-color, lang: "en")

  let ld = state("label-disambiguator", (:))
  let update-ld(k) = ld.update(it => {
    it.insert(k, it.at(k, default: 0) + 1);
    it
  })
  let get-ld(loc, k) = make-unique-label(k, disambiguator: ld.at(loc).at(k))

  // render a dash to hint headings instead of bolding it.
  show heading : set text(weight: "regular") if is-web-target
  show heading : it => {
    block({
      if is-web-target {
        let title = markup-text(it.body).trim();
        update-ld(title)
        context ({
          let loc = here();
          let dest = get-ld(loc, title);
          let h = measure(it.body).height;
          place(left, dx: - 20pt, [
            #set text(fill: dash-color)
            #link(loc)[\#] #dest
          ])
        });
      }
      it
    })
  }

  // link setting
  show link : set text(fill: dash-color)

  // math setting
  show math.equation: set text(weight: 400)

  // code block setting
  show raw: it => {
    set text(font: code-font)
    if "block" in it.fields() and it.block {
      rect(
        width: 100%,
        inset: (x: 4pt, y: 5pt),
        radius: 4pt,
        fill: code-extra-colors.at("bg"),
        [
          #set text(fill: code-extra-colors.at("fg")) if code-extra-colors.at("fg") != none
          #set par(justify: false)
          #place(right, text(luma(110), it.lang))
          #it
        ],
      )
    } else {
      it
    }
  }

  if show-title {
    align(center)[ #block(text(weight: 700, 1.75em, title)) ]
  }

  if authors.len() > 0 {
    // Author information.
    pad(
      top: 0.5em,
      bottom: 0.5em,
      x: 2em,
      grid(
        columns: (1fr,) * calc.min(3, authors.len()),
        gutter: 1em,
        ..authors.map(author => align(center)[
          *#author.name* \
          #author.email
        ]),
      ),
    )
  }

  // Main body.
  set par(justify: true)

  body
}

#let part-style = heading
