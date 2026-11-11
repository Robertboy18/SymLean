/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
-- The duplicate gate of `scripts/dups.sh`, which runs this file after an `import` of every module
-- under `CAS/`. It prints five counts and their lists, one item per line:
--   DUPDEF   groups of library definitions of functions with the same type and value (a value of
--            a type that is not a function type, such as a numeric limit, is not counted);
--   DUPTHM   groups of library theorems with the same statement;
--   RESTATE  library theorems whose statement is that of a theorem outside SymLean;
--   UNUSED   library declarations that no declaration of SymLean uses (examples included), except
--            instances, `simp` and `csimp` lemmas and the targets of `scripts/dups.targets`;
--   EQUIV    library theorems `∀ xs, c₁ xs = c₂ xs` or `↔` between two definitions, at least one
--            of them in the library, applied to exactly the bound variables.
-- The library is `CAS` without `CAS.Examples`. Statements and values are compared as terms, up to
-- the names of bound variables and of universe parameters; a name quoted in meta code (``n``) is
-- a use of `n`. Proofs count: theorem bodies are read with `allowOpaque`. Generated declarations
-- (`_proof_n`, matchers, `eq_n`, `eq_def` and the like) are not counted.

open Lean Meta Compiler

/-- The name that `Name.mkStr p s`, `Name.str p s`, `Name.mkStr1 s₁` … `Name.mkStr8 s₁ … s₈` or
`Name.anonymous` builds from string literals, as quoted names elaborate. -/
partial def nameLiteral? (e : Expr) : Option Name :=
  if e.isConstOf ``Name.anonymous then some .anonymous else
  match e.getAppFn with
  | .const c _ =>
    let args := e.getAppArgs
    let strings := args.filterMap fun
      | .lit (.strVal s) => some s
      | _ => none
    if (c == ``Name.mkStr || c == ``Name.str) && args.size == 2 then
      match nameLiteral? args[0]!, args[1]! with
      | some p, .lit (.strVal s) => some (p.str s)
      | _, _ => none
    else if [``Name.mkStr1, ``Name.mkStr2, ``Name.mkStr3, ``Name.mkStr4, ``Name.mkStr5,
        ``Name.mkStr6, ``Name.mkStr7, ``Name.mkStr8].contains c && 0 < args.size &&
        strings.size == args.size then
      some (strings.foldl Name.str .anonymous)
    else none
  | _ => none

/-- Whether `c` is a constant applied to exactly the bound variables `#(n - 1) … #0`. -/
def appliedToBVars (n : Nat) (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const c _ =>
    let args := e.getAppArgs
    if args.size == n && (List.range n).all fun k ↦ args[k]! == .bvar (n - 1 - k) then some c
    else none
  | _ => none

/-- The groups of more than one name in `m`, each as one sorted, comma-separated line. -/
def groupsOf {α : Type} [BEq α] [Hashable α] (m : Std.HashMap α (Array Name)) : Array String :=
  m.fold (init := #[]) fun acc _ names ↦
    if names.size > 1 then
      acc.push (", ".intercalate ((names.qsort (·.toString < ·.toString)).toList.map toString))
    else acc

/-- The body of `∀ x₁ … xₙ, b` and `n`. -/
def stripForall : Expr → Nat → Expr × Nat
  | .forallE _ _ b _, n => stripForall b (n + 1)
  | e, n => (e, n)

#eval show MetaM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i ↦ env.header.moduleNames[i.toNat]!
  let ours (n : Name) := (modOf n).any (·.getRoot == `CAS)
  let lib (n : Name) := (modOf n).any fun m ↦ m.getRoot == `CAS && !(`CAS.Examples).isPrefixOf m
  let skip (n : Name) := n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    (env.isProjectionFn n) || isMatcherCore env n ||
    (match n with
      | .str _ s => s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "fun_cases"
      | _ => false)
  let canon (c : ConstantInfo) (e : Expr) : Expr :=
    e.instantiateLevelParams c.levelParams
      (c.levelParams.mapIdx fun i _ ↦ .param (.mkSimple s!"u{i}"))
  -- The modules and names whose declarations count as used (downstream users, audit targets).
  let targets : NameSet ←
    try
      let text ← IO.FS.readFile "scripts/dups.targets"
      pure <| text.splitOn "\n" |>.foldl (init := {}) fun s line ↦
        let line := String.ofList ((line.splitOn "#").head!.toList.filter fun ch ↦ !ch.isWhitespace)
        if line.isEmpty then s else s.insert line.toName
    catch _ => pure {}
  let simpLemmas := (simpExtension.getState env).lemmaNames
  let mut defs : Std.HashMap (Expr × Expr) (Array Name) := {}
  let mut thms : Std.HashMap Expr (Array Name) := {}
  let mut external : Std.HashMap Expr Name := {}
  let mut used : NameSet := {}
  let mut candidates : Array Name := #[]
  let mut equivs : Array String := #[]
  for (n, c) in env.constants.map₁.toList do
    let isOurs := ours n
    if isOurs then
      let value? := c.value? (allowOpaque := true)
      for m in c.type.getUsedConstants ++ (value?.map (·.getUsedConstants)).getD #[] do
        if m != n then used := used.insert m
      if let some value := value? then
        let found ← IO.mkRef ({} : NameSet)
        value.forEachWhere (fun e ↦ e.isApp && (e.getAppFn.isConst))
          (fun e ↦ do if let some m := nameLiteral? e then found.modify (·.insert m))
          (stopWhenVisited := false)
        for m in (← found.get).toList do used := used.insert m
    if skip n then continue
    match c with
    | .defnInfo d =>
        if lib n then
          candidates := candidates.push n
          if d.type.isForall then
            let key := (canon c d.type, canon c d.value)
            defs := defs.insert key ((defs.getD key #[]).push n)
    | .thmInfo t =>
        let type := canon c t.type
        if lib n then
          thms := thms.insert type ((thms.getD type #[]).push n)
          candidates := candidates.push n
          let (body, k) := stripForall t.type 0
          let sides? : Option (Expr × Expr) :=
            if body.isAppOfArity ``Eq 3 then some (body.appFn!.appArg!, body.appArg!)
            else if body.isAppOfArity ``Iff 2 then some (body.appFn!.appArg!, body.appArg!)
            else none
          if let some (lhs, rhs) := sides? then
            if let (some c₁, some c₂) := (appliedToBVars k lhs, appliedToBVars k rhs) then
              let isDef (c : Name) := (env.find? c).any (·.isDefinition)
              if c₁ != c₂ && isDef c₁ && isDef c₂ && (lib c₁ || lib c₂) then
                equivs := equivs.push s!"{n}: {c₁} ~ {c₂}"
        else if !isOurs then
          external := external.insert type n
    | _ => pure ()
  let dupDefs := (groupsOf defs).qsort (· < ·)
  let dupThms := (groupsOf thms).qsort (· < ·)
  let restated := (thms.fold (init := #[]) fun acc type names ↦
      match external[type]? with
      | some e => names.foldl (fun acc n ↦ acc.push s!"{n} = {e}") acc
      | none => acc).qsort (· < ·)
  let unused := (candidates.filter fun n ↦
      !used.contains n && !isInstanceCore env n && !hasCSimpAttribute env n &&
      !simpLemmas.contains (.decl n) && !targets.contains n &&
      !(modOf n).any targets.contains).map toString |>.qsort (· < ·)
  let equivLines := equivs.qsort (· < ·)
  IO.println s!"DUPDEF {dupDefs.size}"
  IO.println s!"DUPTHM {dupThms.size}"
  IO.println s!"RESTATE {restated.size}"
  IO.println s!"UNUSED {unused.size}"
  IO.println s!"EQUIV {equivLines.size}"
  for (tag, list) in [("DUPDEF", dupDefs), ("DUPTHM", dupThms), ("RESTATE", restated),
      ("UNUSED", unused), ("EQUIV", equivLines)] do
    for line in list do IO.println s!"{tag}: {line}"
