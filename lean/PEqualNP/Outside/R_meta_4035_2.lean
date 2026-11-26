import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Normalize C via p10_18 (exact size 18, output 28, no NOT(10), ReadsBack, live gates,
-- distinct binary inputs, independent wire-10 readers), then restrict x_0 = false (wire 10 = true)
-- via pv_15 (Petersen minus a vertex) to eliminate every 2-reader OR case and every 1-reader OR
-- case except fan-out-1 into an AND gate.
set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_4035_2
    (p10_18 : ¬ HasCircuitSize 10
      (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (pv_15 : ¬ HasCircuitSize 9
      (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (twoAndReaders :
      let f := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i + 1)) || x (Fin.natAdd 5 i))) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
      let rd := fun (g : Gate) (w : ℕ) =>
        (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)
      ∀ C : Circuit, FanInTwo C → C.size = 18 → C.output = 28 →
        (∀ x, C.eval (List.ofFn x ++ [!x 0]) = f x) →
        (∀ j : Fin C.size, ¬ rd (C.gates.get j) 0) →
        (∀ j : Fin C.size, ∀ w, rd (C.gates.get j) w → w < 11 + j.val) →
        (∀ j : Fin C.size, j.val < 17 → ∃ k : Fin C.size, rd (C.gates.get k) (11 + j.val)) →
        (∃ a b : Fin C.size, a < b ∧
          (C.gates.get a).op = .and ∧ (C.gates.get b).op = .and ∧
          ¬ rd (C.gates.get b) (11 + a.val) ∧
          ∀ j : Fin C.size, rd (C.gates.get j) 10 ↔ j = a ∨ j = b) →
        False)
    (oneReader :
      let f := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i + 1)) || x (Fin.natAdd 5 i))) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
      let rd := fun (g : Gate) (w : ℕ) =>
        (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)
      ∀ C : Circuit, FanInTwo C → C.size = 18 → C.output = 28 →
        (∀ x, C.eval (List.ofFn x ++ [!x 0]) = f x) →
        (∀ j : Fin C.size, ¬ rd (C.gates.get j) 0) →
        (∀ j : Fin C.size, ∀ w, rd (C.gates.get j) w → w < 11 + j.val) →
        (∀ j : Fin C.size, j.val < 17 → ∃ k : Fin C.size, rd (C.gates.get k) (11 + j.val)) →
        (∃ a : Fin C.size, (∀ j : Fin C.size, rd (C.gates.get j) 10 ↔ j = a) ∧
          ((C.gates.get a).op = .and ∨
            ((C.gates.get a).op = .or ∧ ∃ k : Fin C.size, (C.gates.get k).op = .and ∧
              ∀ m : Fin C.size, rd (C.gates.get m) (11 + a.val) ↔ m = k))) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7) := by
  intro C hFan hSize hEval hNo0 hCover
  classical
  let p10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let pv : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  let f : (Fin 10 → Bool) → Bool := fun x => (List.finRange 5).any fun i =>
    (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i + 1)) || x (Fin.natAdd 5 i))) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
  let rd (g : Gate) (w : ℕ) : Prop :=
    (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  let row (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]
  have hEvalP : ∀ x : Fin 10 → Bool, C.eval (row x) = p10 x := hEval
  have f_eq_p10 (x : Fin 10 → Bool) : f x = p10 x := by
    change (((x 0 && (x 1 || x 5) || x 5 && x 7) ||
      ((x 1 && (x 2 || x 6) || x 6 && x 8) ||
      ((x 2 && (x 3 || x 7) || x 7 && x 9) ||
      ((x 3 && (x 4 || x 8) || x 8 && x 5) ||
      ((x 4 && (x 0 || x 9) || x 9 && x 6) || false)))))) = p10 x
    simp only [Bool.or_false, Bool.and_or_distrib_left, p10]
    ac_rfl
  have p10_nonconst : p10 (fun _ => false) = false ∧ p10 (fun _ => true) = true := by
    constructor <;> rfl
  have pv_nonconst : pv (fun _ => false) = false ∧ pv (fun _ => true) = true := by
    constructor <;> rfl
  have run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step w g)).length = w.length + (gs.length + 1)
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = w.getD i false
      have hi' : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih _ hi']
      change (w ++ [_]).getD i false = w.getD i false
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
  -- Prepending NOT(0) converts any size ≤ 17 circuit on 11 inputs into a size ≤ 18 circuit on 10 inputs
  have noSmall11 (D : Circuit) (hD : FanInTwo D) (hDs : D.size ≤ 17)
      (hDe : ∀ x : Fin 10 → Bool, D.eval (row x) = p10 x) : False := by
    let first : Gate := ⟨.not, [0]⟩
    apply p10_18
    refine ⟨⟨first :: D.gates, D.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ first :: D.gates at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr (Or.inr rfl), by decide⟩
      · exact hD g hg
    · change (first :: D.gates).length ≤ 18
      change D.gates.length ≤ 17 at hDs
      simp only [List.length_cons]; omega
    · intro x
      have hFirst : step (List.ofFn x) first = row x := by
        change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = List.ofFn x ++ [!x 0]
        simp [List.getD_eq_getElem?_getD]
      change (run D.gates (step (List.ofFn x) first)).getD D.output false = p10 x
      rw [hFirst]
      exact hDe x
  have hSizeEq : C.size = 18 := by
    by_contra hne
    exact noSmall11 C hFan (by omega) hEval
  have hLenEq : C.gates.length = 18 := hSizeEq
  -- Symbolic simplification / restriction engine
  let evalSym (s : Bool ⊕ ℕ) (w : List Bool) : Bool :=
    Sum.elim id (fun k => w.getD k false) s
  let elimNot (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    List.casesOn vs (Sum.inl (Sum.inl true)) (fun v _ =>
      Sum.elim (fun b => Sum.inl (Sum.inl (!b))) (fun k => Sum.inr ⟨.not, [k]⟩) v)
  let elimAnd (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    List.casesOn vs (Sum.inl (Sum.inl true)) (fun v1 t1 =>
      List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
        List.casesOn t2
          (Sum.elim
            (fun b1 => Bool.casesOn b1 (Sum.inl (Sum.inl false)) (Sum.inl v2))
            (fun k1 => Sum.elim
              (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inl false)) (Sum.inl (Sum.inr k1)))
              (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨.and, [k1, k2]⟩)
              v2)
            v1)
          (fun _ _ => Sum.inl (Sum.inl false))))
  let elimOr (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    List.casesOn vs (Sum.inl (Sum.inl false)) (fun v1 t1 =>
      List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
        List.casesOn t2
          (Sum.elim
            (fun b1 => Bool.casesOn b1 (Sum.inl v2) (Sum.inl (Sum.inl true)))
            (fun k1 => Sum.elim
              (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inr k1)) (Sum.inl (Sum.inl true)))
              (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨.or, [k1, k2]⟩)
              v2)
            v1)
          (fun _ _ => Sum.inl (Sum.inl false))))
  let elimGate (op : GateOp) (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    GateOp.casesOn op (elimAnd vs) (elimOr vs) (elimNot vs)
      (fun _ => Sum.inl (Sum.inl false)) (Sum.inl (Sum.inl false))
  let elimStep (n' : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate × List Bool) (g : Gate) :
      List (Bool ⊕ ℕ) × List Gate × List Bool :=
    let st := acc.1
    let ngs := acc.2.1
    let fl := acc.2.2
    let vs := g.inputs.map fun i => st.getD i (Sum.inl false)
    Sum.elim
      (fun sym => (st ++ [sym], ngs, fl ++ [true]))
      (fun ng => (st ++ [Sum.inr (n' + ngs.length)], ngs ++ [ng], fl ++ [false]))
      (elimGate g.op vs)
  -- Correctness of elimGate (split into inl and inr to avoid match expressions)
  have elimGate_inl (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (B : ℕ)
      (hbd : ∀ s ∈ vs, ∀ k, s = Sum.inr k → k < B) (sym : Bool ⊕ ℕ)
      (heq : elimGate op vs = Sum.inl sym) :
      (∀ k, sym = Sum.inr k → k < B) ∧
      (∀ w : List Bool, evalSym sym w = op.eval (vs.map fun s => evalSym s w)) := by
    have hop' : op = .and ∨ op = .or ∨ op = .not := hop
    rcases hop' with rfl | rfl | rfl
    · cases vs with
      | nil =>
        have h : sym = Sum.inl true := (Sum.inl.inj heq).symm
        subst h; exact ⟨(fun _ hk => by cases hk), (fun _ => rfl)⟩
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          have h : sym = v1 := (Sum.inl.inj heq).symm
          subst h
          refine ⟨fun k hk => hbd sym (List.mem_cons_self ..) k hk, fun w => ?_⟩
          change evalSym sym w = ([evalSym sym w]).all id
          simp
        | cons v2 t2 =>
          cases t2 with
          | nil =>
            cases v1 with
            | inl b1 =>
              cases b1
              · have h : sym = Sum.inl false := (Sum.inl.inj heq).symm
                subst h
                exact ⟨(fun _ hk => by cases hk), (fun w => by
                  change false = ([false, evalSym v2 w]).all id; simp)⟩
              · have h : sym = v2 := (Sum.inl.inj heq).symm
                subst h
                exact ⟨fun k hk => hbd sym (List.mem_cons_of_mem _ (List.mem_cons_self ..)) k hk,
                  fun w => by change evalSym sym w = ([true, evalSym sym w]).all id; simp⟩
            | inr k1 =>
              cases v2 with
              | inl b2 =>
                cases b2
                · have h : sym = Sum.inl false := (Sum.inl.inj heq).symm
                  subst h
                  exact ⟨(fun _ hk => by cases hk), (fun w => by
                    change false = ([w.getD k1 false, false]).all id; simp)⟩
                · have h : sym = Sum.inr k1 := (Sum.inl.inj heq).symm
                  subst h
                  exact ⟨fun k hk => hbd (Sum.inr k1) (List.mem_cons_self ..) k hk,
                    fun w => by change w.getD k1 false = ([w.getD k1 false, true]).all id; simp⟩
              | inr k2 =>
                dsimp only [elimGate, elimAnd, Sum.elim] at heq
                by_cases hkk : k1 = k2
                · subst hkk
                  simp only [ite_true, Sum.inl.injEq] at heq
                  subst heq
                  exact ⟨fun k hk => hbd (Sum.inr k1) (List.mem_cons_self ..) k hk,
                    fun w => by change w.getD k1 false = ([w.getD k1 false, w.getD k1 false]).all id; simp⟩
                · simp only [hkk, ite_false] at heq
                  cases heq
          | cons _ _ => simp at hlen
    · cases vs with
      | nil =>
        have h : sym = Sum.inl false := (Sum.inl.inj heq).symm
        subst h; exact ⟨(fun _ hk => by cases hk), (fun _ => rfl)⟩
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          have h : sym = v1 := (Sum.inl.inj heq).symm
          subst h
          refine ⟨fun k hk => hbd sym (List.mem_cons_self ..) k hk, fun w => ?_⟩
          change evalSym sym w = ([evalSym sym w]).any id
          simp
        | cons v2 t2 =>
          cases t2 with
          | nil =>
            cases v1 with
            | inl b1 =>
              cases b1
              · have h : sym = v2 := (Sum.inl.inj heq).symm
                subst h
                exact ⟨fun k hk => hbd sym (List.mem_cons_of_mem _ (List.mem_cons_self ..)) k hk,
                  fun w => by change evalSym sym w = ([false, evalSym sym w]).any id; simp⟩
              · have h : sym = Sum.inl true := (Sum.inl.inj heq).symm
                subst h
                exact ⟨(fun _ hk => by cases hk), (fun w => by
                  change true = ([true, evalSym v2 w]).any id; simp)⟩
            | inr k1 =>
              cases v2 with
              | inl b2 =>
                cases b2
                · have h : sym = Sum.inr k1 := (Sum.inl.inj heq).symm
                  subst h
                  exact ⟨fun k hk => hbd (Sum.inr k1) (List.mem_cons_self ..) k hk,
                    fun w => by change w.getD k1 false = ([w.getD k1 false, false]).any id; simp⟩
                · have h : sym = Sum.inl true := (Sum.inl.inj heq).symm
                  subst h
                  exact ⟨(fun _ hk => by cases hk), (fun w => by
                    change true = ([w.getD k1 false, true]).any id; simp)⟩
              | inr k2 =>
                dsimp only [elimGate, elimOr, Sum.elim] at heq
                by_cases hkk : k1 = k2
                · subst hkk
                  simp only [ite_true, Sum.inl.injEq] at heq
                  subst heq
                  exact ⟨fun k hk => hbd (Sum.inr k1) (List.mem_cons_self ..) k hk,
                    fun w => by change w.getD k1 false = ([w.getD k1 false, w.getD k1 false]).any id; simp⟩
                · simp only [hkk, ite_false] at heq
                  cases heq
          | cons _ _ => simp at hlen
    · cases vs with
      | nil =>
        have h : sym = Sum.inl true := (Sum.inl.inj heq).symm
        subst h; exact ⟨(fun _ hk => by cases hk), (fun _ => rfl)⟩
      | cons v1 t1 =>
        cases v1 with
        | inl b1 =>
          have h : sym = Sum.inl (!b1) := (Sum.inl.inj heq).symm
          subst h; exact ⟨(fun _ hk => by cases hk), (fun _ => rfl)⟩
        | inr k1 =>
          change Sum.inr _ = Sum.inl sym at heq
          cases heq
  have elimGate_inr (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (ng : Gate)
      (heq : elimGate op vs = Sum.inr ng) :
      (ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ng.inputs.length ≤ 2) ∧
      (∀ w : List Bool, ng.op.eval (ng.inputs.map fun i => w.getD i false) =
        op.eval (vs.map fun s => evalSym s w)) := by
    have hop' : op = .and ∨ op = .or ∨ op = .not := hop
    rcases hop' with rfl | rfl | rfl
    · cases vs with
      | nil => change Sum.inl _ = Sum.inr ng at heq; cases heq
      | cons v1 t1 =>
        cases t1 with
        | nil => change Sum.inl _ = Sum.inr ng at heq; cases heq
        | cons v2 t2 =>
          cases t2 with
          | nil =>
            cases v1 with
            | inl b1 => cases b1 <;> (change Sum.inl _ = Sum.inr ng at heq; cases heq)
            | inr k1 =>
              cases v2 with
              | inl b2 => cases b2 <;> (change Sum.inl _ = Sum.inr ng at heq; cases heq)
              | inr k2 =>
                dsimp only [elimGate, elimAnd, Sum.elim] at heq
                by_cases hkk : k1 = k2
                · simp only [hkk, ite_true] at heq; cases heq
                · simp only [hkk, ite_false, Sum.inr.injEq] at heq
                  subst heq
                  exact ⟨⟨Or.inl rfl, by simp⟩, fun _ => rfl⟩
          | cons _ _ => simp at hlen
    · cases vs with
      | nil => change Sum.inl _ = Sum.inr ng at heq; cases heq
      | cons v1 t1 =>
        cases t1 with
        | nil => change Sum.inl _ = Sum.inr ng at heq; cases heq
        | cons v2 t2 =>
          cases t2 with
          | nil =>
            cases v1 with
            | inl b1 => cases b1 <;> (change Sum.inl _ = Sum.inr ng at heq; cases heq)
            | inr k1 =>
              cases v2 with
              | inl b2 => cases b2 <;> (change Sum.inl _ = Sum.inr ng at heq; cases heq)
              | inr k2 =>
                dsimp only [elimGate, elimOr, Sum.elim] at heq
                by_cases hkk : k1 = k2
                · simp only [hkk, ite_true] at heq; cases heq
                · simp only [hkk, ite_false, Sum.inr.injEq] at heq
                  subst heq
                  exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, fun _ => rfl⟩
          | cons _ _ => simp at hlen
    · cases vs with
      | nil => change Sum.inl _ = Sum.inr ng at heq; cases heq
      | cons v1 t1 =>
        cases v1 with
        | inl b1 => change Sum.inl _ = Sum.inr ng at heq; cases heq
        | inr k1 =>
          have h : ng = ⟨.not, [k1]⟩ := (Sum.inr.inj heq).symm
          subst h
          exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, fun _ => rfl⟩
  -- Invariant of folding elimStep over a gate list
  have elimFold_inv (n' : ℕ) (gs : List Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (st : List (Bool ⊕ ℕ)) (ngs : List Gate) (fl : List Bool)
      (hngsFan : ∀ g ∈ ngs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (hstBd : ∀ s ∈ st, ∀ k, s = Sum.inr k → k < n' + ngs.length) :
      let res := gs.foldl (elimStep n') (st, ngs, fl)
      res.1.length = st.length + gs.length ∧
      res.2.2.length = fl.length + gs.length ∧
      res.2.1.length + (res.2.2.count true) = ngs.length + fl.count true + gs.length ∧
      (∀ g ∈ res.2.1, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ s ∈ res.1, ∀ k, s = Sum.inr k → k < n' + res.2.1.length) ∧
      (∀ i < st.length, res.1.getD i (Sum.inl false) = st.getD i (Sum.inl false)) ∧
      (∀ i < fl.length, res.2.2.getD i false = fl.getD i false) ∧
      (∀ (w u : List Bool), u.length = n' → w.length = st.length →
        (∀ i, w.getD i false = evalSym (st.getD i (Sum.inl false)) (run ngs u)) →
        ∀ i, (run gs w).getD i false = evalSym (res.1.getD i (Sum.inl false)) (run res.2.1 u)) := by
    induction gs generalizing st ngs fl with
    | nil =>
      refine ⟨by simp, by simp, by simp, hngsFan, hstBd, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
      intro w u _ _ h i
      exact h i
    | cons g gs ih =>
      have hg := hgs g (List.mem_cons_self ..)
      have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      let vs := g.inputs.map fun i => st.getD i (Sum.inl false)
      have hvs_len : vs.length ≤ 2 := by simp only [vs, List.length_map]; exact hg.2
      have hvs_bd : ∀ s ∈ vs, ∀ k, s = Sum.inr k → k < n' + ngs.length := by
        intro s hs k hk
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
        by_cases hi : i < st.length
        · have hmem : st.getD i (Sum.inl false) ∈ st := by
            rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
          exact hstBd _ hmem k hk
        · have hdef : st.getD i (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default _ _ (by omega)
          rw [hdef] at hk
          cases hk
      have hstep_res : (g :: gs).foldl (elimStep n') (st, ngs, fl) =
          gs.foldl (elimStep n') (elimStep n' (st, ngs, fl) g) := rfl
      rw [hstep_res]
      cases heg : elimGate g.op vs with
      | inl sym =>
        have hstepEq : elimStep n' (st, ngs, fl) g = (st ++ [sym], ngs, fl ++ [true]) := by
          dsimp only [elimStep]
          change Sum.elim _ _ (elimGate g.op vs) = _
          rw [heg]; rfl
        rw [hstepEq]
        obtain ⟨hsymBd, hsymEv⟩ := elimGate_inl g.op hg.1 vs hvs_len (n' + ngs.length) hvs_bd sym heg
        have hstBd' : ∀ s ∈ st ++ [sym], ∀ k, s = Sum.inr k → k < n' + ngs.length := by
          intro s hs k hk
          rcases List.mem_append.mp hs with h1 | h2
          · exact hstBd s h1 k hk
          · rw [List.mem_singleton.mp h2] at hk; exact hsymBd k hk
        obtain ⟨hL1, hL2, hC, hF, hB, hP1, hP2, hSem⟩ :=
          ih hgs' (st ++ [sym]) ngs (fl ++ [true]) hngsFan hstBd'
        refine ⟨by rw [hL1]; simp; omega, by rw [hL2]; simp; omega, ?_, hF, hB, ?_, ?_, ?_⟩
        · rw [hC, List.count_append, List.count_cons_self, List.count_nil]; simp; omega
        · intro i hi
          rw [hP1 i (by simp; omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
        · intro i hi
          rw [hP2 i (by simp; omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
        · intro w u hu hw hrel i
          change (run gs (step w g)).getD i false = _
          apply hSem (step w g) u hu (by simp [step, hw])
          intro j
          rcases Nat.lt_trichotomy j w.length with hj | rfl | hj
          · have h1 : (step w g).getD j false = w.getD j false := by
              change (w ++ [_]).getD j false = w.getD j false
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD]
            have h2 : (st ++ [sym]).getD j (Sum.inl false) = st.getD j (Sum.inl false) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < st.length),
                ← List.getD_eq_getElem?_getD]
            rw [h1, h2]
            exact hrel j
          · have h1 : (step w g).getD w.length false = g.op.eval (g.inputs.map fun k => w.getD k false) := by
              change (w ++ [_]).getD w.length false = _
              simp [List.getD_eq_getElem?_getD]
            have h2 : (st ++ [sym]).getD w.length (Sum.inl false) = sym := by
              rw [hw]; simp [List.getD_eq_getElem?_getD]
            rw [h1, h2, hsymEv (run ngs u)]
            congr 1
            dsimp only [vs]
            rw [List.map_map]
            apply List.map_congr_left
            intro k _
            exact hrel k
          · have h1 : (step w g).getD j false = false := by
              apply List.getD_eq_default
              simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            have h2 : (st ++ [sym]).getD j (Sum.inl false) = Sum.inl false := by
              apply List.getD_eq_default
              simp only [List.length_append, List.length_cons, List.length_nil]; omega
            rw [h1, h2]; rfl
      | inr ng =>
        have hstepEq : elimStep n' (st, ngs, fl) g =
            (st ++ [Sum.inr (n' + ngs.length)], ngs ++ [ng], fl ++ [false]) := by
          dsimp only [elimStep]
          change Sum.elim _ _ (elimGate g.op vs) = _
          rw [heg]; rfl
        rw [hstepEq]
        obtain ⟨hngFan, hngEv⟩ := elimGate_inr g.op hg.1 vs hvs_len ng heg
        have hngsFan' : ∀ g' ∈ ngs ++ [ng],
            g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
          intro g' hg'
          rcases List.mem_append.mp hg' with h1 | h2
          · exact hngsFan g' h1
          · rw [List.mem_singleton.mp h2]; exact hngFan
        have hstBd' : ∀ s ∈ st ++ [Sum.inr (n' + ngs.length)], ∀ k, s = Sum.inr k →
            k < n' + (ngs ++ [ng]).length := by
          intro s hs k hk
          rw [List.length_append, List.length_singleton]
          rcases List.mem_append.mp hs with h1 | h2
          · have := hstBd s h1 k hk; omega
          · rw [List.mem_singleton.mp h2] at hk
            have := Sum.inr.inj hk; omega
        obtain ⟨hL1, hL2, hC, hF, hB, hP1, hP2, hSem⟩ :=
          ih hgs' (st ++ [Sum.inr (n' + ngs.length)]) (ngs ++ [ng]) (fl ++ [false]) hngsFan' hstBd'
        refine ⟨by rw [hL1]; simp; omega, by rw [hL2]; simp; omega, ?_, hF, hB, ?_, ?_, ?_⟩
        · rw [hC, List.length_append, List.count_append, List.count_cons_of_ne (by decide)]
          simp only [List.length_cons, List.length_nil, List.count_nil]
          omega
        · intro i hi
          rw [hP1 i (by simp; omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
        · intro i hi
          rw [hP2 i (by simp; omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
        · intro w u hu hw hrel i
          change (run gs (step w g)).getD i false = _
          apply hSem (step w g) u hu (by simp [step, hw])
          have hrun_ext : run (ngs ++ [ng]) u = step (run ngs u) ng := by
            dsimp only [run]; rw [List.foldl_append]; rfl
          have hrun_len : (run ngs u).length = n' + ngs.length := by rw [run_len, hu]
          intro j
          rcases Nat.lt_trichotomy j w.length with hj | rfl | hj
          · have h1 : (step w g).getD j false = w.getD j false := by
              change (w ++ [_]).getD j false = w.getD j false
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD]
            have h2 : (st ++ [Sum.inr (n' + ngs.length)]).getD j (Sum.inl false) =
                st.getD j (Sum.inl false) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < st.length),
                ← List.getD_eq_getElem?_getD]
            rw [h1, h2, hrel j]
            have hjst : j < st.length := by omega
            have hmem : st.getD j (Sum.inl false) ∈ st := by
              rw [List.getD_eq_getElem _ _ hjst]; exact List.getElem_mem hjst
            cases hsj : st.getD j (Sum.inl false) with
            | inl b => rfl
            | inr k =>
              have hk : k < (run ngs u).length := by rw [hrun_len]; exact hstBd _ hmem k hsj
              change (run ngs u).getD k false = (run (ngs ++ [ng]) u).getD k false
              rw [hrun_ext]
              change (run ngs u).getD k false = (run ngs u ++ [_]).getD k false
              symm
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
          · have h1 : (step w g).getD w.length false = g.op.eval (g.inputs.map fun k => w.getD k false) := by
              change (w ++ [_]).getD w.length false = _
              simp [List.getD_eq_getElem?_getD]
            have h2 : (st ++ [Sum.inr (n' + ngs.length)]).getD w.length (Sum.inl false) =
                Sum.inr (n' + ngs.length) := by
              rw [hw]; simp [List.getD_eq_getElem?_getD]
            rw [h1, h2]
            change _ = (run (ngs ++ [ng]) u).getD (n' + ngs.length) false
            rw [hrun_ext]
            have hAt : (step (run ngs u) ng).getD (n' + ngs.length) false =
                ng.op.eval (ng.inputs.map fun k => (run ngs u).getD k false) := by
              change (run ngs u ++ [_]).getD (n' + ngs.length) false = _
              rw [← hrun_len]
              simp [List.getD_eq_getElem?_getD]
            rw [hAt, hngEv (run ngs u)]
            congr 1
            dsimp only [vs]
            rw [List.map_map]
            apply List.map_congr_left
            intro k _
            exact hrel k
          · have h1 : (step w g).getD j false = false := by
              apply List.getD_eq_default
              simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            have h2 : (st ++ [Sum.inr (n' + ngs.length)]).getD j (Sum.inl false) = Sum.inl false := by
              apply List.getD_eq_default
              simp only [List.length_append, List.length_cons, List.length_nil]; omega
            rw [h1, h2]; rfl
  -- Inspecting a single step j of elimFold
  have elimFold_at (n' : ℕ) (st0 : List (Bool ⊕ ℕ))
      (hst0Bd : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < n')
      (j : ℕ) (hj : j < C.gates.length) :
      let res := C.gates.foldl (elimStep n') (st0, [], [])
      let pref := (C.gates.take j).foldl (elimStep n') (st0, [], [])
      let g := C.gates[j]
      let vs := g.inputs.map fun i => pref.1.getD i (Sum.inl false)
      (∀ i < st0.length + j, pref.1.getD i (Sum.inl false) = res.1.getD i (Sum.inl false)) ∧
      pref.1.length = st0.length + j ∧
      (∀ sym, elimGate g.op vs = Sum.inl sym →
        res.1.getD (st0.length + j) (Sum.inl false) = sym ∧ res.2.2.getD j false = true) ∧
      (∀ ng, elimGate g.op vs = Sum.inr ng →
        res.1.getD (st0.length + j) (Sum.inl false) = Sum.inr (n' + pref.2.1.length) ∧
        res.2.2.getD j false = false) := by
    let res := C.gates.foldl (elimStep n') (st0, [], [])
    let pref := (C.gates.take j).foldl (elimStep n') (st0, [], [])
    let g := C.gates[j]
    let vs := g.inputs.map fun i => pref.1.getD i (Sum.inl false)
    have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
      have h1 := (List.take_append_drop j C.gates).symm
      rw [List.drop_eq_getElem_cons hj] at h1
      exact h1
    have hres_eq : res = (C.gates.drop (j + 1)).foldl (elimStep n') (elimStep n' pref g) := by
      dsimp only [res, pref]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append]
      rfl
    have htakeFan : ∀ g' ∈ C.gates.take j,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hFan g' (List.mem_of_mem_take hg')
    have hdropFan : ∀ g' ∈ C.gates.drop (j + 1),
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hFan g' (List.mem_of_mem_drop hg')
    obtain ⟨hpL1, hpL2, _, hpFan, hPrefBd, _, _, _⟩ :=
      elimFold_inv n' (C.gates.take j) htakeFan st0 [] [] (fun _ h => absurd h (List.not_mem_nil))
        (by simpa using hst0Bd)
    have hpL1' : pref.1.length = st0.length + j := by
      change pref.1.length = st0.length + (C.gates.take j).length at hpL1
      rw [hpL1, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hpL2' : pref.2.2.length = j := by
      change pref.2.2.length = 0 + (C.gates.take j).length at hpL2
      rw [hpL2, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hgFan := hFan g (List.getElem_mem hj)
    have hvs_bd : ∀ s ∈ vs, ∀ k, s = Sum.inr k → k < n' + pref.2.1.length := by
      intro s hs k hk
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
      by_cases hi : i < pref.1.length
      · exact hPrefBd _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi) k hk
      · rw [List.getD_eq_default _ _ (by omega)] at hk; cases hk
    have hStepMeta : (elimStep n' pref g).1.length = st0.length + j + 1 ∧
        (elimStep n' pref g).2.2.length = j + 1 ∧
        (∀ g' ∈ (elimStep n' pref g).2.1,
          g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
        (∀ s ∈ (elimStep n' pref g).1, ∀ k, s = Sum.inr k → k < n' + (elimStep n' pref g).2.1.length) ∧
        (∀ i < st0.length + j, (elimStep n' pref g).1.getD i (Sum.inl false) = pref.1.getD i (Sum.inl false)) := by
      cases heg : elimGate g.op vs with
      | inl sym =>
        have hEq : elimStep n' pref g = (pref.1 ++ [sym], pref.2.1, pref.2.2 ++ [true]) := by
          dsimp only [elimStep]; change Sum.elim _ _ (elimGate g.op vs) = _; rw [heg]; rfl
        rw [hEq]
        obtain ⟨hsymBd, _⟩ := elimGate_inl g.op hgFan.1 vs (by simp [vs, hgFan.2]) (n' + pref.2.1.length) hvs_bd sym heg
        refine ⟨by simp [hpL1'], by simp [hpL2'], hpFan, ?_, ?_⟩
        · intro s hs k hk
          rcases List.mem_append.mp hs with h1 | h2
          · exact hPrefBd s h1 k hk
          · rw [List.mem_singleton.mp h2] at hk; exact hsymBd k hk
        · intro i hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pref.1.length),
            ← List.getD_eq_getElem?_getD]
      | inr ng =>
        have hEq : elimStep n' pref g =
            (pref.1 ++ [Sum.inr (n' + pref.2.1.length)], pref.2.1 ++ [ng], pref.2.2 ++ [false]) := by
          dsimp only [elimStep]; change Sum.elim _ _ (elimGate g.op vs) = _; rw [heg]; rfl
        rw [hEq]
        obtain ⟨hngFan, _⟩ := elimGate_inr g.op hgFan.1 vs (by simp [vs, hgFan.2]) ng heg
        refine ⟨by simp [hpL1'], by simp [hpL2'], ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with h1 | h2
          · exact hpFan g' h1
          · rw [List.mem_singleton.mp h2]; exact hngFan
        · intro s hs k hk
          rw [List.length_append, List.length_singleton]
          rcases List.mem_append.mp hs with h1 | h2
          · have hlt := hPrefBd s h1 k hk
            change k < n' + pref.2.1.length at hlt
            omega
          · rw [List.mem_singleton.mp h2] at hk; have := Sum.inr.inj hk; omega
        · intro i hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pref.1.length),
            ← List.getD_eq_getElem?_getD]
    obtain ⟨hSL1, hSL2, hSFan, hSBd, hSPref⟩ := hStepMeta
    obtain ⟨_, _, _, _, _, hTailP1, hTailP2, _⟩ :=
      elimFold_inv n' (C.gates.drop (j + 1)) hdropFan
        (elimStep n' pref g).1 (elimStep n' pref g).2.1 (elimStep n' pref g).2.2 hSFan hSBd
    refine ⟨?_, hpL1', ?_, ?_⟩
    · intro i hi
      change pref.1.getD i (Sum.inl false) = res.1.getD i (Sum.inl false)
      rw [hres_eq, hTailP1 i (by omega), hSPref i hi]
    · intro sym heg
      have hEq : elimStep n' pref g = (pref.1 ++ [sym], pref.2.1, pref.2.2 ++ [true]) := by
        dsimp only [elimStep]; change Sum.elim _ _ (elimGate g.op vs) = _; rw [heg]; rfl
      constructor
      · change res.1.getD (st0.length + j) (Sum.inl false) = sym
        rw [hres_eq, hTailP1 (st0.length + j) (by omega), hEq]
        change (pref.1 ++ [sym]).getD (st0.length + j) (Sum.inl false) = sym
        rw [← hpL1']; simp [List.getD_eq_getElem?_getD]
      · change res.2.2.getD j false = true
        rw [hres_eq, hTailP2 j (by omega), hEq]
        change (pref.2.2 ++ [true]).getD j false = true
        rw [← hpL2']; simp [List.getD_eq_getElem?_getD]
    · intro ng heg
      have hEq : elimStep n' pref g =
          (pref.1 ++ [Sum.inr (n' + pref.2.1.length)], pref.2.1 ++ [ng], pref.2.2 ++ [false]) := by
        dsimp only [elimStep]; change Sum.elim _ _ (elimGate g.op vs) = _; rw [heg]; rfl
      constructor
      · change res.1.getD (st0.length + j) (Sum.inl false) = Sum.inr (n' + pref.2.1.length)
        rw [hres_eq, hTailP1 (st0.length + j) (by omega), hEq]
        change (pref.1 ++ [Sum.inr (n' + pref.2.1.length)]).getD (st0.length + j) (Sum.inl false) = _
        rw [← hpL1']; simp [List.getD_eq_getElem?_getD]
      · change res.2.2.getD j false = false
        rw [hres_eq, hTailP2 j (by omega), hEq]
        change (pref.2.2 ++ [false]).getD j false = false
        rw [← hpL2']; simp [List.getD_eq_getElem?_getD]
  -- RUN 1: 11-input cleanup via elimStep
  let st11 : List (Bool ⊕ ℕ) := (List.range 11).map Sum.inr
  have hst11Len : st11.length = 11 := by simp [st11]
  have hst11Bd : ∀ s ∈ st11, ∀ k, s = Sum.inr k → k < 11 := by
    intro s hs k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    have hi' : i < 11 := List.mem_range.mp hi
    have := Sum.inr.inj hk; omega
  let res1 := C.gates.foldl (elimStep 11) (st11, [], [])
  obtain ⟨h1L1, h1L2, h1Cnt, h1Fan, _, h1P1, _, h1Sem⟩ :=
    elimFold_inv 11 C.gates hFan st11 [] [] (fun _ h => absurd h (List.not_mem_nil)) (by simpa using hst11Bd)
  have h1Count0 : res1.2.2.count true = 0 := by
    by_contra hne
    have hsz17 : res1.2.1.length ≤ 17 := by
      change res1.2.1.length + res1.2.2.count true = 0 + 0 + C.gates.length at h1Cnt
      omega
    have hInitRel (x : Fin 10 → Bool) (i : ℕ) :
        (row x).getD i false = evalSym (st11.getD i (Sum.inl false)) (run [] (row x)) := by
      by_cases hi : i < 11
      · have hget : st11.getD i (Sum.inl false) = Sum.inr i := by
          rw [List.getD_eq_getElem _ _ (by omega : i < st11.length)]
          simp [st11]
        rw [hget]; rfl
      · rw [List.getD_eq_default _ _ (by simp [row]; omega),
          List.getD_eq_default _ _ (by omega : st11.length ≤ i)]
        rfl
    have hOutEv (x : Fin 10 → Bool) :
        p10 x = evalSym (res1.1.getD C.output (Sum.inl false)) (run res1.2.1 (row x)) := by
      rw [← hEvalP x]
      exact h1Sem (row x) (row x) (by simp [row]) (by simp [row, hst11Len]) (hInitRel x) C.output
    cases hout : res1.1.getD C.output (Sum.inl false) with
    | inl b =>
      have hf := hOutEv (fun _ => false)
      have ht := hOutEv (fun _ => true)
      rw [hout] at hf ht
      rw [p10_nonconst.1] at hf
      rw [p10_nonconst.2] at ht
      change false = b at hf
      change true = b at ht
      rw [← hf] at ht
      exact Bool.noConfusion ht
    | inr outW =>
      apply noSmall11 ⟨res1.2.1, outW⟩ h1Fan hsz17
      intro x
      have hx := hOutEv x
      rw [hout] at hx
      exact hx.symm
  have h1AllFalse (j : ℕ) (hj : j < C.gates.length) : res1.2.2.getD j false = false := by
    have hnot : true ∉ res1.2.2 := List.count_eq_zero.mp h1Count0
    have hmem : res1.2.2.getD j false ∈ res1.2.2 := by
      rw [List.getD_eq_getElem _ _ (by change res1.2.2.length = 0 + C.gates.length at h1L2; omega)]
      exact List.getElem_mem _
    cases h : res1.2.2.getD j false with
    | false => rfl
    | true => rw [h] at hmem; exact (hnot hmem).elim
  have h1ReadsBack_and_shape (j : Fin C.gates.length) :
      (∀ w, rd (C.gates.get j) w → w < 11 + j.val) ∧
      ((C.gates.get j).op ≠ .not → ∃ u v, (C.gates.get j).inputs = [u, v] ∧
        u < 11 + j.val ∧ v < 11 + j.val ∧ u ≠ v) := by
    obtain ⟨hPrefEq, hPrefLen, hInl, _⟩ := elimFold_at 11 st11 hst11Bd j.val j.isLt
    let pref := (C.gates.take j.val).foldl (elimStep 11) (st11, [], [])
    change pref.1.length = st11.length + j.val at hPrefLen
    rw [hst11Len] at hPrefLen
    let g := C.gates[j.val]
    let vs := g.inputs.map fun i => pref.1.getD i (Sum.inl false)
    have hNotInl : ∀ sym, elimGate g.op vs ≠ Sum.inl sym := by
      intro sym heq
      have ht := (hInl sym heq).2
      have hf := h1AllFalse j.val j.isLt
      rw [hf] at ht
      exact Bool.noConfusion ht
    have hPrefId (i : ℕ) (hi : i < 11 + j.val) : pref.1.getD i (Sum.inl false) = Sum.inr i := by
      by_cases hi11 : i < 11
      · rw [hPrefEq i (by omega), h1P1 i (by omega)]
        rw [List.getD_eq_getElem _ _ (by omega : i < st11.length)]
        simp [st11]
      · let t := i - 11
        have htLt : t < C.gates.length := by omega
        obtain ⟨_, _, htInl, htInr⟩ := elimFold_at 11 st11 hst11Bd t htLt
        have htTakeFan : ∀ g' ∈ C.gates.take t,
            g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hFan g' (List.mem_of_mem_take hg')
        have htDropFan : ∀ g' ∈ C.gates.drop t,
            g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hFan g' (List.mem_of_mem_drop hg')
        obtain ⟨_, htl2, htCnt, htFan, htBd, _, _, _⟩ :=
          elimFold_inv 11 (C.gates.take t) htTakeFan st11 [] [] (fun _ h => absurd h (List.not_mem_nil))
            (by simpa using hst11Bd)
        let tp := (C.gates.take t).foldl (elimStep 11) (st11, [], [])
        obtain ⟨_, _, _, _, _, _, htDropP2, _⟩ :=
          elimFold_inv 11 (C.gates.drop t) htDropFan tp.1 tp.2.1 tp.2.2 htFan htBd
        have hresSplit : res1 = (C.gates.drop t).foldl (elimStep 11) tp := by
          dsimp only [res1, tp]
          conv_lhs => rw [← List.take_append_drop t C.gates]
          rw [List.foldl_append]
        have htCnt0 : tp.2.2.count true = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          obtain ⟨q, hq, hqEq⟩ := List.mem_iff_getElem.mp hmem
          have hqLt : q < t := by
            change tp.2.2.length = 0 + (C.gates.take t).length at htl2
            rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt htLt)] at htl2
            omega
          have hq1 : res1.2.2.getD q false = true := by
            rw [hresSplit, htDropP2 q hq, List.getD_eq_getElem _ _ hq]
            exact hqEq
          have hq2 := h1AllFalse q (by omega)
          rw [hq2] at hq1
          exact Bool.noConfusion hq1
        cases hte : elimGate C.gates[t].op
            (C.gates[t].inputs.map fun q => tp.1.getD q (Sum.inl false)) with
        | inl sym =>
          have h1 := (htInl sym hte).2
          rw [h1AllFalse t htLt] at h1
          exact Bool.noConfusion h1
        | inr ng =>
          have h1 := (htInr ng hte).1
          rw [hPrefEq i (by omega)]
          have hiEq : 11 + t = i := by omega
          rw [hst11Len, hiEq] at h1
          have hngsEq : tp.2.1.length = t := by
            change tp.2.1.length + tp.2.2.count true = 0 + 0 + (C.gates.take t).length at htCnt
            rw [htCnt0, List.length_take, Nat.min_eq_left (Nat.le_of_lt htLt)] at htCnt
            omega
          rw [hngsEq] at h1
          simpa [hiEq] using h1
    have hgFan := hFan g (List.getElem_mem j.isLt)
    have hgetEq : C.gates.get j = g := by simp [g]
    rw [hgetEq]
    have hop' : g.op = .and ∨ g.op = .or ∨ g.op = .not := hgFan.1
    rcases hop' with hand | hor | hnot
    · have hlen2 : g.inputs.length = 2 := by
        have hle := hgFan.2
        cases hin : g.inputs with
        | nil => exact (hNotInl (Sum.inl true) (by simp [elimGate, elimAnd, hand, vs, hin])).elim
        | cons u t1 =>
          cases t1 with
          | nil =>
            exact (hNotInl (pref.1.getD u (Sum.inl false)) (by simp [elimGate, elimAnd, hand, vs, hin])).elim
          | cons v t2 =>
            cases t2 with
            | nil => rfl
            | cons _ _ => rw [hin] at hle; simp at hle
      obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlen2
      have hvs2 : vs = [pref.1.getD u (Sum.inl false), pref.1.getD v (Sum.inl false)] := by
        dsimp only [vs]; rw [huv]; rfl
      have hu : u < 11 + j.val := by
        by_contra hge
        have hdef : pref.1.getD u (Sum.inl false) = Sum.inl false :=
          List.getD_eq_default _ _ (by omega)
        exact hNotInl (Sum.inl false) (by rw [hand, hvs2, hdef]; rfl)
      have hv : v < 11 + j.val := by
        by_contra hge
        have hdef : pref.1.getD v (Sum.inl false) = Sum.inl false :=
          List.getD_eq_default _ _ (by omega)
        exact hNotInl (Sum.inl false) (by rw [hand, hvs2, hPrefId u hu, hdef]; rfl)
      have hne : u ≠ v := by
        intro heq
        subst heq
        exact hNotInl (Sum.inr u) (by rw [hand, hvs2, hPrefId u hu]; simp [elimGate, elimAnd])
      refine ⟨?_, fun _ => ⟨u, v, huv, hu, hv, hne⟩⟩
      intro w hw
      rcases hw with ⟨hn, _⟩ | ⟨_, hmem⟩
      · rw [hand] at hn; exact GateOp.noConfusion hn
      · rw [huv] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> assumption
    · have hlen2 : g.inputs.length = 2 := by
        have hle := hgFan.2
        cases hin : g.inputs with
        | nil => exact (hNotInl (Sum.inl false) (by simp [elimGate, elimOr, hor, vs, hin])).elim
        | cons u t1 =>
          cases t1 with
          | nil =>
            exact (hNotInl (pref.1.getD u (Sum.inl false)) (by simp [elimGate, elimOr, hor, vs, hin])).elim
          | cons v t2 =>
            cases t2 with
            | nil => rfl
            | cons _ _ => rw [hin] at hle; simp at hle
      obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlen2
      have hvs2 : vs = [pref.1.getD u (Sum.inl false), pref.1.getD v (Sum.inl false)] := by
        dsimp only [vs]; rw [huv]; rfl
      have hu : u < 11 + j.val := by
        by_contra hge
        have hdef : pref.1.getD u (Sum.inl false) = Sum.inl false :=
          List.getD_eq_default _ _ (by omega)
        exact hNotInl (pref.1.getD v (Sum.inl false)) (by rw [hor, hvs2, hdef]; rfl)
      have hv : v < 11 + j.val := by
        by_contra hge
        have hdef : pref.1.getD v (Sum.inl false) = Sum.inl false :=
          List.getD_eq_default _ _ (by omega)
        exact hNotInl (Sum.inr u) (by rw [hor, hvs2, hPrefId u hu, hdef]; rfl)
      have hne : u ≠ v := by
        intro heq
        subst heq
        exact hNotInl (Sum.inr u) (by rw [hor, hvs2, hPrefId u hu]; simp [elimGate, elimOr])
      refine ⟨?_, fun _ => ⟨u, v, huv, hu, hv, hne⟩⟩
      intro w hw
      rcases hw with ⟨hn, _⟩ | ⟨_, hmem⟩
      · rw [hor] at hn; exact GateOp.noConfusion hn
      · rw [huv] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> assumption
    · refine ⟨?_, fun hne => (hne hnot).elim⟩
      intro w hw
      rcases hw with ⟨_, hhead⟩ | ⟨hne, _⟩
      · cases hin : g.inputs with
        | nil => rw [hin] at hhead; cases hhead
        | cons u t =>
          rw [hin, List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          by_contra hge
          have hdef : pref.1.getD u (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default _ _ (by omega)
          have hvs1 : vs = pref.1.getD u (Sum.inl false) :: t.map (fun i => pref.1.getD i (Sum.inl false)) := by
            dsimp only [vs]; rw [hin]; rfl
          exact hNotInl (Sum.inl true) (by rw [hnot, hvs1, hdef]; rfl)
      · exact (hne hnot).elim
  have hReadsBack : ∀ j : Fin C.gates.length, ∀ w, rd (C.gates.get j) w → w < 11 + j.val :=
    fun j => (h1ReadsBack_and_shape j).1
  have hBinShape : ∀ j : Fin C.gates.length, (C.gates.get j).op ≠ .not →
      ∃ u v, (C.gates.get j).inputs = [u, v] ∧ u < 11 + j.val ∧ v < 11 + j.val ∧ u ≠ v :=
    fun j => (h1ReadsBack_and_shape j).2
  -- Helper: gate evaluation on `row x` using `hReadsBack`
  have run_gate_row (k : Fin C.gates.length) (x : Fin 10 → Bool) :
      (run C.gates (row x)).getD (11 + k.val) false =
        (C.gates.get k).op.eval ((C.gates.get k).inputs.map fun u => (run C.gates (row x)).getD u false) := by
    have hsplit : C.gates = C.gates.take k.val ++ C.gates[k.val] :: C.gates.drop (k.val + 1) := by
      have h1 := (List.take_append_drop k.val C.gates).symm
      rw [List.drop_eq_getElem_cons k.isLt] at h1
      exact h1
    have hrowLen : (row x).length = 11 := by simp [row]
    have hplen : (run (C.gates.take k.val) (row x)).length = 11 + k.val := by
      rw [run_len, hrowLen, List.length_take, Nat.min_eq_left (Nat.le_of_lt k.isLt)]
    have hstep : run C.gates (row x) =
        run (C.gates.drop (k.val + 1)) (step (run (C.gates.take k.val) (row x)) C.gates[k.val]) := by
      dsimp only [run]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append]
      rfl
    have hk' : 11 + k.val < (step (run (C.gates.take k.val) (row x)) C.gates[k.val]).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil, hplen]; omega
    have hget : (run C.gates (row x)).getD (11 + k.val) false =
        C.gates[k.val].op.eval (C.gates[k.val].inputs.map fun u => (run (C.gates.take k.val) (row x)).getD u false) := by
      rw [hstep, run_preserves _ _ _ hk']
      change (run (C.gates.take k.val) (row x) ++
        [C.gates[k.val].op.eval (C.gates[k.val].inputs.map fun u => (run (C.gates.take k.val) (row x)).getD u false)]).getD
        (11 + k.val) false = _
      have hsnoc : (run (C.gates.take k.val) (row x) ++
          [C.gates[k.val].op.eval (C.gates[k.val].inputs.map fun u => (run (C.gates.take k.val) (row x)).getD u false)]).getD
          (run (C.gates.take k.val) (row x)).length false =
          C.gates[k.val].op.eval (C.gates[k.val].inputs.map fun u => (run (C.gates.take k.val) (row x)).getD u false) := by
        simp [List.getD_eq_getElem?_getD]
      simpa only [hplen] using hsnoc
    have hagree (u : ℕ) (hu : u < 11 + k.val) :
        (run (C.gates.take k.val) (row x)).getD u false = (run C.gates (row x)).getD u false := by
      have hu' : u < (step (run (C.gates.take k.val) (row x)) C.gates[k.val]).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil, hplen]; omega
      rw [hstep, run_preserves _ _ _ hu']
      change (run (C.gates.take k.val) (row x)).getD u false = (run (C.gates.take k.val) (row x) ++ [_]).getD u false
      symm
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < (run (C.gates.take k.val) (row x)).length),
        ← List.getD_eq_getElem?_getD]
    have hgetEq : C.gates.get k = C.gates[k.val] := rfl
    rw [hgetEq, hget]
    by_cases hnot : C.gates[k.val].op = .not
    · rw [hnot]
      cases hin : C.gates[k.val].inputs with
      | nil => rfl
      | cons u t =>
        have hu : u < 11 + k.val := hReadsBack k u (Or.inl ⟨hnot, by simp [hin]⟩)
        change (!((run (C.gates.take k.val) (row x)).getD u false)) = (!((run C.gates (row x)).getD u false))
        rw [hagree u hu]
    · congr 1
      apply List.map_congr_left
      intro u hu
      exact hagree u (hReadsBack k u (Or.inr ⟨hnot, hu⟩))
  -- Unified 11-input gate erasure (kills dead gates, output ≠ 28, and alias gates!)
  have erase11_contrad (m : Fin C.gates.length) (r : ℕ) (hr : r < 11 + m.val)
      (hCond : (C.output ≠ 11 + m.val ∧ ∀ k : Fin C.gates.length, ¬ rd (C.gates.get k) (11 + m.val)) ∨
        (∀ x : Fin 10 → Bool, (run C.gates (row x)).getD (11 + m.val) false = (run C.gates (row x)).getD r false)) :
      False := by
    let fR := fun i : ℕ => if i = 11 + m.val then r else if 11 + m.val < i then i - 1 else i
    let mapG := fun g : Gate => Gate.mk g.op (g.inputs.map fR)
    let gs' := C.gates.take m.val ++ (C.gates.drop (m.val + 1)).map mapG
    have hFan' : FanInTwo ⟨gs', fR C.output⟩ := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hFan g (List.mem_of_mem_take h1)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
        obtain ⟨hop, hlen⟩ := hFan g0 (List.mem_of_mem_drop hg0)
        exact ⟨hop, by simpa [mapG] using hlen⟩
    have hSize' : (Circuit.mk gs' (fR C.output)).size ≤ 17 := by
      change (C.gates.take m.val ++ (C.gates.drop (m.val + 1)).map mapG).length ≤ 17
      rw [List.length_append, List.length_take, List.length_map, List.length_drop,
        Nat.min_eq_left (Nat.le_of_lt m.isLt)]
      omega
    have hEv' (x : Fin 10 → Bool) : (Circuit.mk gs' (fR C.output)).eval (row x) = p10 x := by
      rw [← hEvalP x]
      -- Prove agreement on every wire w (or every wire ≠ 11 + m.val)
      have hSim : ∀ (gs : List Gate) (w v : List Bool),
          11 + m.val ≤ v.length → w.length = v.length + 1 →
          (∀ g ∈ gs, ∀ u, rd g u → u ≠ 11 + m.val ∨
            (w.getD (11 + m.val) false = v.getD r false)) →
          (∀ i, (i ≠ 11 + m.val ∨ w.getD (11 + m.val) false = v.getD r false) →
            v.getD (fR i) false = w.getD i false) →
          ∀ i, (i ≠ 11 + m.val ∨ w.getD (11 + m.val) false = v.getD r false) →
            (run (gs.map mapG) v).getD (fR i) false = (run gs w).getD i false := by
        intro gs
        induction gs with
        | nil => intro w v _ _ _ h i hi; exact h i hi
        | cons g gs ih =>
          intro w v hmv hwl hgate hlook i hi
          change (run (gs.map mapG) (step v (mapG g))).getD (fR i) false =
            (run gs (step w g)).getD i false
          have hvalEq : (mapG g).op.eval ((mapG g).inputs.map fun u => v.getD u false) =
              g.op.eval (g.inputs.map fun u => w.getD u false) := by
            by_cases hnot : g.op = .not
            · change g.op.eval ((g.inputs.map fR).map fun u => v.getD u false) =
                g.op.eval (g.inputs.map fun u => w.getD u false)
              rw [hnot]
              cases hin : g.inputs with
              | nil => rfl
              | cons u t =>
                have hu := hgate g (List.mem_cons_self ..) u (Or.inl ⟨hnot, by simp [hin]⟩)
                change (!(v.getD (fR u) false)) = (!(w.getD u false))
                rw [hlook u hu]
            · change g.op.eval ((g.inputs.map fR).map fun u => v.getD u false) = _
              rw [List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              exact hlook u (hgate g (List.mem_cons_self ..) u (Or.inr ⟨hnot, hu⟩))
          have hStepKeep : (step w g).getD (11 + m.val) false = w.getD (11 + m.val) false ∧
              (step v (mapG g)).getD r false = v.getD r false := by
            constructor
            · change (w ++ [_]).getD (11 + m.val) false = w.getD (11 + m.val) false
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : 11 + m.val < w.length),
                ← List.getD_eq_getElem?_getD]
            · change (v ++ [_]).getD r false = v.getD r false
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : r < v.length),
                ← List.getD_eq_getElem?_getD]
          apply ih (step w g) (step v (mapG g))
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
            (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
            (fun g' hg' u hu => by
              rw [hStepKeep.1, hStepKeep.2]
              exact hgate g' (List.mem_cons_of_mem _ hg') u hu)
          · intro j hj
            rw [hStepKeep.1, hStepKeep.2] at hj
            rcases Nat.lt_trichotomy j w.length with hlt | rfl | hgt
            · have hfLt : fR j < v.length := by dsimp only [fR]; split_ifs <;> omega
              change (v ++ [_]).getD (fR j) false = (w ++ [_]).getD j false
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hfLt, ← List.getD_eq_getElem?_getD]
              symm
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
              exact (hlook j hj).symm
            · have hfEq : fR w.length = v.length := by dsimp only [fR]; split_ifs <;> omega
              change (v ++ [_]).getD (fR w.length) false = (w ++ [_]).getD w.length false
              rw [hfEq]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              exact hvalEq
            · have hfGe : (step v (mapG g)).length ≤ fR j := by
                simp only [step, List.length_append, List.length_cons, List.length_nil]
                dsimp only [fR]; split_ifs <;> omega
              have hjGe : (step w g).length ≤ j := by
                simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
              rw [List.getD_eq_default _ _ hfGe, List.getD_eq_default _ _ hjGe]
          · rw [hStepKeep.1, hStepKeep.2]; exact hi
      let v := run (C.gates.take m.val) (row x)
      let w := step v C.gates[m.val]
      have hvLen : v.length = 11 + m.val := by
        rw [run_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt m.isLt)]
        simp [row]
      have hOld : run C.gates (row x) = run (C.gates.drop (m.val + 1)) w := by
        have hsplit : C.gates = C.gates.take m.val ++ C.gates[m.val] :: C.gates.drop (m.val + 1) := by
          have h1 := (List.take_append_drop m.val C.gates).symm
          rw [List.drop_eq_getElem_cons m.isLt] at h1
          exact h1
        dsimp only [run, w, v]
        conv_lhs => rw [hsplit]
        rw [List.foldl_append]; rfl
      have hNew : run gs' (row x) = run ((C.gates.drop (m.val + 1)).map mapG) v := by
        dsimp only [run, gs', v]
        rw [List.foldl_append]
      have hKeepMid : w.getD (11 + m.val) false = (run C.gates (row x)).getD (11 + m.val) false ∧
          v.getD r false = (run C.gates (row x)).getD r false := by
        have hwLen : w.length = 11 + m.val + 1 := by
          simp only [w, step, List.length_append, List.length_cons, List.length_nil, hvLen]
        constructor
        · symm; rw [hOld, run_preserves _ _ _ (by omega)]
        · symm
          rw [hOld, run_preserves _ _ _ (by omega)]
          change (v ++ [_]).getD r false = v.getD r false
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : r < v.length), ← List.getD_eq_getElem?_getD]
      have hBase (i : ℕ) (hi : i ≠ 11 + m.val ∨ w.getD (11 + m.val) false = v.getD r false) :
          v.getD (fR i) false = w.getD i false := by
        rcases Nat.lt_trichotomy i (11 + m.val) with hlt | rfl | hgt
        · have hfi : fR i = i := by dsimp only [fR]; split_ifs <;> omega
          rw [hfi]
          change v.getD i false = (v ++ [_]).getD i false
          symm
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < v.length), ← List.getD_eq_getElem?_getD]
        · rcases hi with hne | heq
          · exact (hne rfl).elim
          · have hfi : fR (11 + m.val) = r := by dsimp only [fR]; simp
            rw [hfi]; exact heq.symm
        · have hfi : fR i = i - 1 := by dsimp only [fR]; split_ifs <;> omega
          rw [hfi, List.getD_eq_default _ _ (by omega : v.length ≤ i - 1),
            List.getD_eq_default _ _ (by simp only [w, step, List.length_append, List.length_cons, List.length_nil, hvLen]; omega)]
      change (run gs' (row x)).getD (fR C.output) false = (run C.gates (row x)).getD C.output false
      rw [hNew, hOld]
      apply hSim (C.gates.drop (m.val + 1)) w v (by omega)
        (by simp only [w, step, List.length_append, List.length_cons, List.length_nil])
      · intro g hg u hu
        rcases hCond with ⟨_, hNoRd⟩ | hAlias
        · left
          intro hEq
          subst hEq
          have hgMem : g ∈ C.gates := List.mem_of_mem_drop hg
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hgMem
          exact hNoRd ⟨k, hk⟩ hu
        · right
          rw [hKeepMid.1, hKeepMid.2]
          exact hAlias x
      · exact hBase
      · rcases hCond with ⟨hOutNe, _⟩ | hAlias
        · exact Or.inl hOutNe
        · right; rw [hKeepMid.1, hKeepMid.2]; exact hAlias x
    exact noSmall11 ⟨gs', fR C.output⟩ hFan' hSize' hEv'
  -- Dead gate elimination => output = 28 and every gate < 17 has a reader!
  have hOut28 : C.output = 28 := by
    by_contra hne
    let last : Fin C.gates.length := ⟨17, by omega⟩
    apply erase11_contrad last 0 (by omega)
    left
    refine ⟨hne, fun k hr => ?_⟩
    have hlt := hReadsBack k (11 + last.val) hr
    have hklt := k.isLt
    change 11 + 17 < 11 + k.val at hlt
    omega
  have hLive (j : Fin C.gates.length) (hj : j.val < 17) :
      ∃ k : Fin C.gates.length, rd (C.gates.get k) (11 + j.val) := by
    by_contra hnone
    push Not at hnone
    exact erase11_contrad j 0 (by omega) (Or.inl ⟨by omega, hnone⟩)
  -- No NOT gate reads wire 10 (reroute to wire 0 -> HasCircuitSize 10 p10 18)
  have hNoNot10 (j : Fin C.gates.length) (hop : (C.gates.get j).op = .not) :
      (C.gates.get j).inputs.head? ≠ some 10 := by
    intro hhead
    -- On every x, gate j outputs !(!x 0) = x 0 = wire 0!
    -- So gate j is an alias of wire 0!!
    apply erase11_contrad j 0 (by omega)
    right
    intro x
    rw [run_gate_row j x, hop]
    cases hin : (C.gates.get j).inputs with
    | nil => rw [hin] at hhead; cases hhead
    | cons u t =>
      rw [hin, List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      change (!((run C.gates (row x)).getD 10 false)) = (run C.gates (row x)).getD 0 false
      rw [run_preserves _ _ 10 (by simp [row]), run_preserves _ _ 0 (by simp [row])]
      simp [row, List.getD_eq_getElem?_getD]
  -- Independent wire-10 readers: if a < b both read 10, b cannot also read 11 + a!
  have hIndep10 (a b : Fin C.gates.length) (hab : a < b)
      (ha : rd (C.gates.get a) 10) (hb : rd (C.gates.get b) 10) :
      ¬ rd (C.gates.get b) (11 + a.val) := by
    intro hba
    have haNot : (C.gates.get a).op ≠ .not := fun h => by
      rcases ha with ⟨_, hh⟩ | ⟨hn, _⟩
      · exact hNoNot10 a h hh
      · exact hn h
    have hbNot : (C.gates.get b).op ≠ .not := fun h => by
      rcases hb with ⟨_, hh⟩ | ⟨hn, _⟩
      · exact hNoNot10 b h hh
      · exact hn h
    obtain ⟨u1, v1, haIn, _, _, _⟩ := hBinShape a haNot
    obtain ⟨u2, v2, hbIn, _, _, hbNe⟩ := hBinShape b hbNot
    have h10a : 10 = u1 ∨ 10 = v1 := by
      rcases ha with ⟨hn, _⟩ | ⟨_, hm⟩
      · exact (haNot hn).elim
      · rw [haIn] at hm; simpa using hm
    have h10b : 10 = u2 ∨ 10 = v2 := by
      rcases hb with ⟨hn, _⟩ | ⟨_, hm⟩
      · exact (hbNot hn).elim
      · rw [hbIn] at hm; simpa using hm
    have habIn : 11 + a.val = u2 ∨ 11 + a.val = v2 := by
      rcases hba with ⟨hn, _⟩ | ⟨_, hm⟩
      · exact (hbNot hn).elim
      · rw [hbIn] at hm; simpa using hm
    have hPairB : (u2 = 10 ∧ v2 = 11 + a.val) ∨ (u2 = 11 + a.val ∧ v2 = 10) := by
      rcases h10b with rfl | rfl <;> rcases habIn with h | h
      · omega
      · exact Or.inl ⟨rfl, h.symm⟩
      · exact Or.inr ⟨h.symm, rfl⟩
      · omega
    have haOp : (C.gates.get a).op = .and ∨ (C.gates.get a).op = .or := by
      have h := (hFan _ (List.get_mem _ a)).1
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (haNot h).elim
    have hbOp : (C.gates.get b).op = .and ∨ (C.gates.get b).op = .or := by
      have h := (hFan _ (List.get_mem _ b)).1
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hbNot h).elim
    -- In all 4 cases of (a.op, b.op), b equals either wire 10 or wire 11 + a!
    have hAlias : (∀ x : Fin 10 → Bool,
        (run C.gates (row x)).getD (11 + b.val) false = (run C.gates (row x)).getD 10 false) ∨
      (∀ x : Fin 10 → Bool,
        (run C.gates (row x)).getD (11 + b.val) false = (run C.gates (row x)).getD (11 + a.val) false) := by
      have hAbsorb : ∀ (op1 op2 : GateOp), (op1 = .and ∨ op1 = .or) → (op2 = .and ∨ op2 = .or) →
          (∀ p q : Bool, op2.eval [p, op1.eval [p, q]] = p ∧ op2.eval [op1.eval [p, q], p] = p ∧
            op2.eval [p, op1.eval [q, p]] = p ∧ op2.eval [op1.eval [q, p], p] = p) ∨
          (∀ p q : Bool, op2.eval [p, op1.eval [p, q]] = op1.eval [p, q] ∧
            op2.eval [op1.eval [p, q], p] = op1.eval [p, q] ∧
            op2.eval [p, op1.eval [q, p]] = op1.eval [q, p] ∧
            op2.eval [op1.eval [q, p], p] = op1.eval [q, p]) := by
        intro op1 op2 h1 h2
        rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
        · right; intro p q; cases p <;> cases q <;> decide
        · left; intro p q; cases p <;> cases q <;> decide
        · left; intro p q; cases p <;> cases q <;> decide
        · right; intro p q; cases p <;> cases q <;> decide
      rcases hAbsorb (C.gates.get a).op (C.gates.get b).op haOp hbOp with hEq10 | hEqA
      · left; intro x
        rw [run_gate_row b x, hbIn]
        simp only [List.map_cons, List.map_nil]
        rcases hPairB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [run_gate_row a x, haIn]; simp only [List.map_cons, List.map_nil]
          rcases h10a with rfl | rfl
          · exact (hEq10 _ _).1
          · exact (hEq10 _ _).2.2.1
        · rw [run_gate_row a x, haIn]; simp only [List.map_cons, List.map_nil]
          rcases h10a with rfl | rfl
          · exact (hEq10 _ _).2.1
          · exact (hEq10 _ _).2.2.2
      · right; intro x
        rw [run_gate_row b x, hbIn]
        simp only [List.map_cons, List.map_nil]
        rcases hPairB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [run_gate_row a x, haIn]; simp only [List.map_cons, List.map_nil]
          rcases h10a with rfl | rfl
          · exact (hEqA _ _).1
          · exact (hEqA _ _).2.2.1
        · rw [run_gate_row a x, haIn]; simp only [List.map_cons, List.map_nil]
          rcases h10a with rfl | rfl
          · exact (hEqA _ _).2.1
          · exact (hEqA _ _).2.2.2
    rcases hAlias with h10 | hA
    · exact erase11_contrad b 10 (by omega) (Or.inr h10)
    · exact erase11_contrad b (11 + a.val) (by have : a.val < b.val := hab; omega) (Or.inr hA)
  -- RUN 2: 9-input restriction x_0 = false (wire 10 = true) => Petersen minus a vertex (pv)
  let embed (y : Fin 9 → Bool) (i : Fin 10) : Bool :=
    ([false, y 6, y 8, y 5, y 7, y 4, y 1, y 3, y 0, y 2]).getD i.val false
  have embed_ok (y : Fin 9 → Bool) : p10 (embed y) = pv y := by
    change ((false && y 6) || (y 6 && y 8) || (y 8 && y 5) || (y 5 && y 7) || (y 7 && false) ||
      (false && y 4) || (y 6 && y 1) || (y 8 && y 3) || (y 5 && y 0) || (y 7 && y 2) ||
      (y 4 && y 3) || (y 3 && y 2) || (y 2 && y 1) || (y 1 && y 0) || (y 0 && y 4)) = pv y
    simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, pv]
    ac_rfl
  let stPv : List (Bool ⊕ ℕ) :=
    [Sum.inl false, Sum.inr 6, Sum.inr 8, Sum.inr 5, Sum.inr 7,
     Sum.inr 4, Sum.inr 1, Sum.inr 3, Sum.inr 0, Sum.inr 2, Sum.inl true]
  have hstPvLen : stPv.length = 11 := rfl
  have hstPvBd : ∀ s ∈ stPv, ∀ k, s = Sum.inr k → k < 9 := by
    intro s hs k hk
    simp only [stPv, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hk
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · have := Sum.inr.inj hk; omega
    · cases hk
  let res2 := C.gates.foldl (elimStep 9) (stPv, [], [])
  obtain ⟨h2L1, h2L2, h2Cnt, h2Fan, _, h2P1, _, h2Sem⟩ :=
    elimFold_inv 9 C.gates hFan stPv [] [] (fun _ h => absurd h (List.not_mem_nil)) (by simpa using hstPvBd)
  have hInitPv (y : Fin 9 → Bool) (i : ℕ) :
      (row (embed y)).getD i false = evalSym (stPv.getD i (Sum.inl false)) (run [] (List.ofFn y)) := by
    by_cases hi : i < 11
    · have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [row, embed, stPv, evalSym, run, List.foldl_nil, List.getD_eq_getElem?_getD,
          List.getElem?_append_left, List.getElem?_append_right, List.getElem?_ofFn, List.length_ofFn,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Sum.elim_inl, Sum.elim_inr, id_eq,
          Option.getD_some, dite_true, Nat.le_refl, Nat.sub_self, Bool.not_false] <;>
        rfl
    · rw [List.getD_eq_default _ _ (by simp [row]; omega),
        List.getD_eq_default _ _ (by omega : stPv.length ≤ i)]
      rfl
  have hOutPv (y : Fin 9 → Bool) :
      pv y = evalSym (res2.1.getD C.output (Sum.inl false)) (run res2.2.1 (List.ofFn y)) := by
    rw [← embed_ok y, ← hEvalP (embed y)]
    exact h2Sem (row (embed y)) (List.ofFn y) (by simp) (by simp [row, hstPvLen]) (hInitPv y) C.output
  have hOutNotConst : ∀ b : Bool, res2.1.getD C.output (Sum.inl false) ≠ Sum.inl b := by
    intro b hb
    have hf := hOutPv (fun _ => false)
    have ht := hOutPv (fun _ => true)
    rw [hb] at hf ht
    rw [pv_nonconst.1] at hf
    rw [pv_nonconst.2] at ht
    change false = b at hf
    change true = b at ht
    rw [← hf] at ht
    exact Bool.noConfusion ht
  have hElimLe2 : res2.2.2.count true ≤ 2 := by
    by_contra hgt
    have hsz15 : res2.2.1.length ≤ 15 := by
      change res2.2.1.length + res2.2.2.count true = 0 + 0 + C.gates.length at h2Cnt
      omega
    cases hout : res2.1.getD C.output (Sum.inl false) with
    | inl b => exact hOutNotConst b hout
    | inr outW =>
      apply pv_15
      refine ⟨⟨res2.2.1, outW⟩, h2Fan, hsz15, fun y => ?_⟩
      have hy := hOutPv y
      rw [hout] at hy
      exact hy.symm
  have hCountGe3 (a b c : Fin C.gates.length) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : res2.2.2.getD a.val false = true)
      (hb : res2.2.2.getD b.val false = true)
      (hc : res2.2.2.getD c.val false = true) : False := by
    have hlen2 : res2.2.2.length = C.gates.length := by
      change res2.2.2.length = 0 + C.gates.length at h2L2; omega
    have hcount_eq : ∀ (l : List Bool),
        l.count true = ((Finset.univ : Finset (Fin l.length)).filter fun i => l.getD i.val false = true).card := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ih =>
        have hstep_card : ((Finset.univ : Finset (Fin (xs.length + 1))).filter
            fun i => (x :: xs).getD i.val false = true).card =
            (if x = true then 1 else 0) +
            ((Finset.univ : Finset (Fin xs.length)).filter fun i => xs.getD i.val false = true).card := by
          let S := (Finset.univ : Finset (Fin (xs.length + 1))).filter fun i => (x :: xs).getD i.val false = true
          let S0 := S.filter fun i => i.val = 0
          let S1 := S.filter fun i => i.val ≠ 0
          have hpart : S.card = S0.card + S1.card := by
            rw [← Finset.card_union_of_disjoint]
            · congr 1; ext i; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]; tauto
            · exact Finset.disjoint_left.mpr fun i h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          have hS0 : S0.card = if x = true then 1 else 0 := by
            by_cases hx : x = true
            · rw [ite_eq_left hx]
              have : S0 = {0} := by
                ext i; simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                constructor
                · rintro ⟨_, h0⟩; exact Fin.ext h0
                · rintro rfl; exact ⟨by simp [hx], rfl⟩
              rw [this]; simp
            · rw [ite_eq_right hx]
              have : S0 = ∅ := by
                ext i; simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rintro ⟨h1, h0⟩
                rw [h0] at h1
                exact hx h1
              rw [this]; simp
          have hS1 : S1.card =
              ((Finset.univ : Finset (Fin xs.length)).filter fun i => xs.getD i.val false = true).card := by
            apply Finset.card_bij (fun i hi => ⟨i.val - 1, by
              have h0 : i.val ≠ 0 := (Finset.mem_filter.mp hi).2
              omega⟩)
            · intro i hi
              simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              obtain ⟨h1, h0⟩ := hi
              cases hv : i.val with
              | zero => exact (h0 hv).elim
              | succ n => rw [hv] at h1; simpa using h1
            · intro i1 hi1 i2 hi2 heq
              have h1 : i1.val ≠ 0 := (Finset.mem_filter.mp hi1).2
              have h2 : i2.val ≠ 0 := (Finset.mem_filter.mp hi2).2
              have hv : i1.val - 1 = i2.val - 1 := congrArg Fin.val heq
              exact Fin.ext (by omega)
            · intro j hj
              refine ⟨⟨j.val + 1, by omega⟩, ?_, Fin.ext (by simp)⟩
              simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              exact ⟨hj, by omega⟩
          rw [hpart, hS0, hS1]
        rw [List.count_cons, ih]
        change _ = ((Finset.univ : Finset (Fin (xs.length + 1))).filter
          fun i => (x :: xs).getD i.val false = true).card
        rw [hstep_card]
        cases x
        · simp
        · simp; omega
    let f2 (x : Fin C.gates.length) : Fin res2.2.2.length := ⟨x.val, by omega⟩
    let T : Finset (Fin res2.2.2.length) := {f2 a, f2 b, f2 c}
    have hTsub : T ⊆ (Finset.univ : Finset (Fin res2.2.2.length)).filter
        fun i => res2.2.2.getD i.val false = true := by
      intro i hi
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hi with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hTcard : T.card = 3 := by
      have h1 : f2 a ≠ f2 b := fun h => hab (Fin.ext (congrArg (fun z : Fin res2.2.2.length => z.val) h))
      have h2 : f2 a ≠ f2 c := fun h => hac (Fin.ext (congrArg (fun z : Fin res2.2.2.length => z.val) h))
      have h3 : f2 b ≠ f2 c := fun h => hbc (Fin.ext (congrArg (fun z : Fin res2.2.2.length => z.val) h))
      simp [T, h1, h2, h3]
    have hle := Finset.card_le_card hTsub
    rw [hTcard, ← hcount_eq res2.2.2] at hle
    omega
  -- Key lemma on Run 2: any gate reading a constant wire in res2 is eliminated, and OR(true)/NOT propagates constants!
  have hConstElim (j : Fin C.gates.length) (w : ℕ) (b : Bool)
      (hrd : rd (C.gates.get j) w) (hst : res2.1.getD w (Sum.inl false) = Sum.inl b) :
      res2.2.2.getD j.val false = true ∧
      ((C.gates.get j).op = .or → b = true → res2.1.getD (11 + j.val) (Sum.inl false) = Sum.inl true) ∧
      ((C.gates.get j).op = .not → res2.1.getD (11 + j.val) (Sum.inl false) = Sum.inl (!b)) := by
    obtain ⟨hPrefEq, _, hInl, _⟩ := elimFold_at 9 stPv hstPvBd j.val j.isLt
    let pref := (C.gates.take j.val).foldl (elimStep 9) (stPv, [], [])
    let g := C.gates[j.val]
    let vs := g.inputs.map fun i => pref.1.getD i (Sum.inl false)
    have hwLt : w < 11 + j.val := hReadsBack j w hrd
    have hwPref : pref.1.getD w (Sum.inl false) = Sum.inl b := by
      rw [hPrefEq w (by rw [hstPvLen]; exact hwLt), hst]
    have hgetEq : C.gates.get j = g := rfl
    rw [hgetEq] at hrd ⊢
    have hop' : g.op = .and ∨ g.op = .or ∨ g.op = .not := (hFan g (List.getElem_mem j.isLt)).1
    rcases hop' with hand | hor | hnot
    · obtain ⟨u, v, huv, _, _, _⟩ := hBinShape j (fun h => by rw [hgetEq, hand] at h; cases h)
      rw [hgetEq] at huv
      have hvs2 : vs = [pref.1.getD u (Sum.inl false), pref.1.getD v (Sum.inl false)] := by
        dsimp only [vs]; rw [huv]; rfl
      have hwMem : w = u ∨ w = v := by
        rcases hrd with ⟨hn, _⟩ | ⟨_, hm⟩
        · rw [hand] at hn; exact GateOp.noConfusion hn
        · rw [huv] at hm; simpa using hm
      have hExInl : ∃ sym, elimGate g.op vs = Sum.inl sym := by
        rcases hwMem with rfl | rfl
        · cases b
          · exact ⟨Sum.inl false, by rw [hand, hvs2, hwPref]; rfl⟩
          · exact ⟨pref.1.getD v (Sum.inl false), by rw [hand, hvs2, hwPref]; rfl⟩
        · cases hpu : pref.1.getD u (Sum.inl false) with
          | inl b1 =>
            cases b1
            · exact ⟨Sum.inl false, by rw [hand, hvs2, hpu, hwPref]; rfl⟩
            · exact ⟨Sum.inl b, by rw [hand, hvs2, hpu, hwPref]; rfl⟩
          | inr k1 =>
            cases b
            · exact ⟨Sum.inl false, by rw [hand, hvs2, hpu, hwPref]; rfl⟩
            · exact ⟨Sum.inr k1, by rw [hand, hvs2, hpu, hwPref]; rfl⟩
      obtain ⟨sym, hsym⟩ := hExInl
      exact ⟨(hInl sym hsym).2,
        fun h => (GateOp.noConfusion (hand.symm.trans h)),
        fun h => (GateOp.noConfusion (hand.symm.trans h))⟩
    · obtain ⟨u, v, huv, _, _, _⟩ := hBinShape j (fun h => by rw [hgetEq, hor] at h; cases h)
      rw [hgetEq] at huv
      have hvs2 : vs = [pref.1.getD u (Sum.inl false), pref.1.getD v (Sum.inl false)] := by
        dsimp only [vs]; rw [huv]; rfl
      have hwMem : w = u ∨ w = v := by
        rcases hrd with ⟨hn, _⟩ | ⟨_, hm⟩
        · rw [hor] at hn; exact GateOp.noConfusion hn
        · rw [huv] at hm; simpa using hm
      rcases b with _ | _
      · have hExInl : ∃ sym, elimGate g.op vs = Sum.inl sym := by
          rcases hwMem with rfl | rfl
          · exact ⟨pref.1.getD v (Sum.inl false), by rw [hor, hvs2, hwPref]; rfl⟩
          · cases hpu : pref.1.getD u (Sum.inl false) with
            | inl b1 =>
              cases b1
              · exact ⟨Sum.inl false, by rw [hor, hvs2, hpu, hwPref]; rfl⟩
              · exact ⟨Sum.inl true, by rw [hor, hvs2, hpu, hwPref]; rfl⟩
            | inr k1 =>
              exact ⟨Sum.inr k1, by rw [hor, hvs2, hpu, hwPref]; rfl⟩
        obtain ⟨sym, hsym⟩ := hExInl
        exact ⟨(hInl sym hsym).2, fun _ h => Bool.noConfusion h,
          fun h => (GateOp.noConfusion (hor.symm.trans h))⟩
      · have hEqTrue : elimGate g.op vs = Sum.inl (Sum.inl true) := by
          rcases hwMem with rfl | rfl
          · rw [hor, hvs2, hwPref]; rfl
          · cases hpu : pref.1.getD u (Sum.inl false) with
            | inl b1 => cases b1 <;> (rw [hor, hvs2, hpu, hwPref]; rfl)
            | inr k1 => rw [hor, hvs2, hpu, hwPref]; rfl
        obtain ⟨hs1, hs2⟩ := hInl (Sum.inl true) hEqTrue
        exact ⟨hs2, fun _ _ => hs1, fun h => (GateOp.noConfusion (hor.symm.trans h))⟩
    · have hhead : g.inputs.head? = some w := by
        rcases hrd with ⟨_, hh⟩ | ⟨hne, _⟩
        · exact hh
        · exact (hne hnot).elim
      cases hin : g.inputs with
      | nil => rw [hin] at hhead; cases hhead
      | cons u t =>
        rw [hin, List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        have hvs1 : vs = pref.1.getD u (Sum.inl false) :: t.map (fun i => pref.1.getD i (Sum.inl false)) := by
          dsimp only [vs]; rw [hin]; rfl
        have hEqNot : elimGate g.op vs = Sum.inl (Sum.inl (!b)) := by
          rw [hnot, hvs1, hwPref]; rfl
        obtain ⟨hs1, hs2⟩ := hInl (Sum.inl (!b)) hEqNot
        exact ⟨hs2, fun h => (GateOp.noConfusion (hnot.symm.trans h)), fun _ => hs1⟩
  have hNotConstGate (j : Fin C.gates.length) (b : Bool)
      (h : res2.1.getD (11 + j.val) (Sum.inl false) = Sum.inl b) : j.val < 17 := by
    by_contra hge
    have hEq28 : 11 + j.val = C.output := by omega
    rw [hEq28] at h
    exact hOutNotConst b h
  have h10True : res2.1.getD 10 (Sum.inl false) = Sum.inl true := by
    rw [h2P1 10 (by omega)]; rfl
  -- Step 5: Wire 10 must have at least 1 reader
  have hNo0Rd (j : Fin C.gates.length) : ¬ rd (C.gates.get j) 0 := by
    rintro (⟨hop, hh⟩ | ⟨hop, hm⟩)
    · exact (hNo0 j).1 hop hh
    · exact (hNo0 j).2 hop hm
  have hHasReader10 : ∃ j : Fin C.gates.length, rd (C.gates.get j) 10 := by
    by_contra hnone
    push Not at hnone
    let hi : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
    let lo : Fin 10 → Bool := fun i => decide (i = 1)
    have hSame : ∀ (gs : List Gate) (w v : List Bool),
        w.length = v.length →
        (∀ g ∈ gs, ¬ rd g 0 ∧ ¬ rd g 10) →
        (∀ i, i ≠ 0 → i ≠ 10 → w.getD i false = v.getD i false) →
        ∀ i, i ≠ 0 → i ≠ 10 → (run gs w).getD i false = (run gs v).getD i false := by
      intro gs
      induction gs with
      | nil => intro w v _ _ h; exact h
      | cons g gs ih =>
        intro w v hwl hno hlook i hi0 hi10
        change (run gs (step w g)).getD i false = (run gs (step v g)).getD i false
        have hgn := hno g (List.mem_cons_self ..)
        have hstepEq : g.op.eval (g.inputs.map fun u => w.getD u false) =
            g.op.eval (g.inputs.map fun u => v.getD u false) := by
          by_cases hn : g.op = .not
          · rw [hn]
            cases hin : g.inputs with
            | nil => rfl
            | cons u t =>
              have hu0 : u ≠ 0 := fun h => hgn.1 (Or.inl ⟨hn, by simp [hin, h]⟩)
              have hu10 : u ≠ 10 := fun h => hgn.2 (Or.inl ⟨hn, by simp [hin, h]⟩)
              change (!(w.getD u false)) = (!(v.getD u false))
              rw [hlook u hu0 hu10]
          · congr 1
            apply List.map_congr_left
            intro u hu
            exact hlook u (fun h => hgn.1 (Or.inr ⟨hn, h ▸ hu⟩)) (fun h => hgn.2 (Or.inr ⟨hn, h ▸ hu⟩))
        apply ih (step w g) (step v g) (by simp [step, hwl])
          (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
        · intro j hj0 hj10
          rcases Nat.lt_trichotomy j w.length with hlt | rfl | hgt
          · change (w ++ [_]).getD j false = (v ++ [_]).getD j false
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
            symm
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < v.length),
              ← List.getD_eq_getElem?_getD]
            exact (hlook j hj0 hj10).symm
          · change (w ++ [_]).getD w.length false = (v ++ [_]).getD w.length false
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hwl,
              List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            exact hstepEq
          · rw [List.getD_eq_default _ _ (by simp [step]; omega),
              List.getD_eq_default _ _ (by simp [step]; omega)]
        · exact hi0
        · exact hi10
    have hStart (i : ℕ) (h0 : i ≠ 0) (h10 : i ≠ 10) : (row hi).getD i false = (row lo).getD i false := by
      have hfin : ∀ k : Fin 11, k.val ≠ 0 → k.val ≠ 10 →
          (row hi).getD k.val false = (row lo).getD k.val false := by decide
      by_cases hlt : i < 11
      · exact hfin ⟨i, hlt⟩ h0 h10
      · rw [List.getD_eq_default _ _ (by simp [row]; omega),
          List.getD_eq_default _ _ (by simp [row]; omega)]
    have hEqOut := hSame C.gates (row hi) (row lo) (by simp [row])
      (fun g hg => by
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
        exact ⟨hNo0Rd ⟨k, hk⟩, hnone ⟨k, hk⟩⟩)
      hStart C.output (by omega) (by omega)
    have h1 : (run C.gates (row hi)).getD C.output false = true := (hEval hi).trans (by decide)
    have h2 : (run C.gates (row lo)).getD C.output false = false := (hEval lo).trans (by decide)
    rw [h1, h2] at hEqOut
    exact Bool.noConfusion hEqOut
  -- Extract the exact reader set (1 or 2 gates) from hCover
  obtain ⟨p, q, hPQ⟩ := hCover
  have hPQrd (j : Fin C.gates.length) (hr : rd (C.gates.get j) 10) : j = p ∨ j = q := by
    rcases hr with ⟨hop, hh⟩ | ⟨hop, hm⟩
    · exact (hPQ j).1 hop hh
    · exact (hPQ j).2 hop hm
  have hEvalF (x : Fin 10 → Bool) : C.eval (List.ofFn x ++ [!x 0]) = f x :=
    (hEval x).trans (f_eq_p10 x).symm
  -- Split into 2 distinct readers vs 1 reader
  by_cases hTwo : ∃ a b : Fin C.gates.length, a < b ∧
      ∀ j : Fin C.gates.length, rd (C.gates.get j) 10 ↔ j = a ∨ j = b
  · obtain ⟨a, b, hab, hAB⟩ := hTwo
    have haRd : rd (C.gates.get a) 10 := (hAB a).mpr (Or.inl rfl)
    have hbRd : rd (C.gates.get b) 10 := (hAB b).mpr (Or.inr rfl)
    have hInd := hIndep10 a b hab haRd hbRd
    have haElim := hConstElim a 10 true haRd h10True
    have hbElim := hConstElim b 10 true hbRd h10True
    have haOp : (C.gates.get a).op = .and ∨ (C.gates.get a).op = .or := by
      rcases (hFan _ (List.get_mem _ a)).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rcases haRd with ⟨_, hh⟩ | ⟨hn, _⟩
        · exact (hNoNot10 a h hh).elim
        · exact (hn h).elim
    have hbOp : (C.gates.get b).op = .and ∨ (C.gates.get b).op = .or := by
      rcases (hFan _ (List.get_mem _ b)).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rcases hbRd with ⟨_, hh⟩ | ⟨hn, _⟩
        · exact (hNoNot10 b h hh).elim
        · exact (hn h).elim
    rcases haOp with haAnd | haOr
    · rcases hbOp with hbAnd | hbOr
      · exact twoAndReaders C hFan hSizeEq hOut28 hEvalF hNo0Rd hReadsBack hLive
          ⟨a, b, hab, haAnd, hbAnd, hInd, hAB⟩
      · have hbTrue := hbElim.2.1 hbOr rfl
        have hbLt17 := hNotConstGate b true hbTrue
        obtain ⟨k, hkRd⟩ := hLive b hbLt17
        have hbk : b.val < k.val := by have := hReadsBack k (11 + b.val) hkRd; omega
        have hkElim := hConstElim k (11 + b.val) true hkRd hbTrue
        have habVal : a.val < b.val := hab
        exact hCountGe3 a b k
          (fun h => by omega)
          (fun h => by have := congrArg Fin.val h; omega)
          (fun h => by have := congrArg Fin.val h; omega)
          haElim.1 hbElim.1 hkElim.1
    · have haTrue := haElim.2.1 haOr rfl
      have haLt17 : a.val < 17 := by have : a.val < b.val := hab; omega
      obtain ⟨k, hkRd⟩ := hLive a haLt17
      have hak : a.val < k.val := by have := hReadsBack k (11 + a.val) hkRd; omega
      have hkb : k ≠ b := fun h => hInd (h ▸ hkRd)
      have hkElim := hConstElim k (11 + a.val) true hkRd haTrue
      have habVal : a.val < b.val := hab
      exact hCountGe3 a b k
        (fun h => by have := congrArg Fin.val h; omega)
        (fun h => by have := congrArg Fin.val h; omega)
        hkb.symm
        haElim.1 hbElim.1 hkElim.1
  · -- Exactly 1 reader `a` of wire 10!
    obtain ⟨a, haRd⟩ := hHasReader10
    have hUniqueA : ∀ j : Fin C.gates.length, rd (C.gates.get j) 10 ↔ j = a := by
      intro j
      constructor
      · intro hj
        by_contra hne
        apply hTwo
        have hOnly : ∀ t : Fin C.gates.length, rd (C.gates.get t) 10 ↔ t = a ∨ t = j := by
          intro t
          constructor
          · intro ht
            rcases hPQrd a haRd with rfl | rfl
            · rcases hPQrd j hj with hja | rfl
              · exact (hne hja).elim
              · exact hPQrd t ht
            · rcases hPQrd j hj with rfl | hja
              · exact (hPQrd t ht).symm
              · exact (hne hja).elim
          · rintro (rfl | rfl) <;> assumption
        rcases Nat.lt_trichotomy a.val j.val with hlt | heq | hgt
        · exact ⟨a, j, hlt, hOnly⟩
        · exact (hne (Fin.ext heq.symm)).elim
        · exact ⟨j, a, hgt, fun t => (hOnly t).trans or_comm⟩
      · rintro rfl; exact haRd
    have haOp : (C.gates.get a).op = .and ∨ (C.gates.get a).op = .or := by
      rcases (hFan _ (List.get_mem _ a)).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rcases haRd with ⟨_, hh⟩ | ⟨hn, _⟩
        · exact (hNoNot10 a h hh).elim
        · exact (hn h).elim
    rcases haOp with haAnd | haOr
    · exact oneReader C hFan hSizeEq hOut28 hEvalF hNo0Rd hReadsBack hLive
        ⟨a, hUniqueA, Or.inl haAnd⟩
    · have haElim := hConstElim a 10 true haRd h10True
      have haTrue := haElim.2.1 haOr rfl
      have haLt17 := hNotConstGate a true haTrue
      obtain ⟨k, hkRd⟩ := hLive a haLt17
      have hak : a.val < k.val := by have := hReadsBack k (11 + a.val) hkRd; omega
      by_cases hTwoK : ∃ k2 : Fin C.gates.length, k2 ≠ k ∧ rd (C.gates.get k2) (11 + a.val)
      · obtain ⟨k2, hk2ne, hk2Rd⟩ := hTwoK
        have hak2 : a.val < k2.val := by have := hReadsBack k2 (11 + a.val) hk2Rd; omega
        have hkElim := hConstElim k (11 + a.val) true hkRd haTrue
        have hk2Elim := hConstElim k2 (11 + a.val) true hk2Rd haTrue
        exact hCountGe3 a k k2
          (fun h => by have := congrArg Fin.val h; omega)
          (fun h => by have := congrArg Fin.val h; omega)
          hk2ne.symm
          haElim.1 hkElim.1 hk2Elim.1
      · push Not at hTwoK
        have hUniqueK : ∀ m : Fin C.gates.length, rd (C.gates.get m) (11 + a.val) ↔ m = k :=
          fun m => ⟨fun hm => by_contra fun hne => hTwoK m hne hm, fun h => h ▸ hkRd⟩
        have hkElim := hConstElim k (11 + a.val) true hkRd haTrue
        have hkOp : (C.gates.get k).op = .and ∨ (C.gates.get k).op = .or ∨ (C.gates.get k).op = .not :=
          (hFan _ (List.get_mem _ k)).1
        rcases hkOp with hkAnd | hkOr | hkNot
        · exact oneReader C hFan hSizeEq hOut28 hEvalF hNo0Rd hReadsBack hLive
            ⟨a, hUniqueA, Or.inr ⟨haOr, k, hkAnd, hUniqueK⟩⟩
        · have hkTrue := hkElim.2.1 hkOr rfl
          have hkLt17 := hNotConstGate k true hkTrue
          obtain ⟨m, hmRd⟩ := hLive k hkLt17
          have hkm : k.val < m.val := by have := hReadsBack m (11 + k.val) hmRd; omega
          have hmElim := hConstElim m (11 + k.val) true hmRd hkTrue
          exact hCountGe3 a k m
            (fun h => by have := congrArg Fin.val h; omega)
            (fun h => by have := congrArg Fin.val h; omega)
            (fun h => by have := congrArg Fin.val h; omega)
            haElim.1 hkElim.1 hmElim.1
        · have hkFalse := hkElim.2.2 hkNot
          have hkLt17 := hNotConstGate k false hkFalse
          obtain ⟨m, hmRd⟩ := hLive k hkLt17
          have hkm : k.val < m.val := by have := hReadsBack m (11 + k.val) hmRd; omega
          have hmElim := hConstElim m (11 + k.val) false hmRd hkFalse
          exact hCountGe3 a k m
            (fun h => by have := congrArg Fin.val h; omega)
            (fun h => by have := congrArg Fin.val h; omega)
            (fun h => by have := congrArg Fin.val h; omega)
            haElim.1 hkElim.1 hmElim.1

