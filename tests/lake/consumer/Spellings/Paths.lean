module

public import CAS.IncludeStr

/-! The spellings of an `include_str` path that the build tracks, each embedding a file of
`data/`. -/

public def nextLine : String := include_str
  "data/next-line.txt"

public def commented : String := include_str /- a "quoted" comment -/ "data/commented.txt"

/-- A gap of several lines, with a line comment and nested block comments. -/
public def nested : String := include_str -- the file of nested comments
  /- an outer /- and an inner -/ comment, with "quotes" -/
  "data/nested.txt"

public def escaped : String := include_str "data/esc\x61ped.txt"

public def gap : String := include_str "data/\
    gap.txt"

public def raw : String := include_str r#"data/raw.txt"#

public def rawPlain : String := include_str r"data/raw-plain.txt"

public def deep : String := include_str "data/sub/deep.txt"
