import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25452_aux

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

theorem step_length (w : List Bool) (g : Gate) :
    (step w g).length = w.length + 1 := by
  simp [step]

theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step_length, List.length_cons]
    omega

theorem getD_append_left {l1 l2 : List Bool} {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_right {l1 l2 : List Bool} {i : ℕ} (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem step_getD_lt (w : List Bool) (g : Gate) {i : ℕ} (hi : i < w.length) :
    (step w g).getD i false = w.getD i false :=
  getD_append_left hi

theorem step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (step w g).length := by rw [step_length]; omega
    rw [ih (step w g) hlt, step_getD_lt w g hi]

def GateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def GatesRB (base : ℕ) (gs : List Gate) : Prop :=
  ∀ j, (hj : j < gs.length) → ∀ i ∈ gs[j].inputs, i < base + j

theorem gatesRB_nil (base : ℕ) : GatesRB base [] := by
  intro j hj; simp at hj

theorem gatesRB_cons {base : ℕ} {g : Gate} {gs : List Gate}
    (hg : ∀ i ∈ g.inputs, i < base) (hgs : GatesRB (base + 1) gs) :
    GatesRB base (g :: gs) := by
  intro j hj i hi
  cases j with
  | zero =>
    simp only [List.getElem_cons_zero] at hi
    simpa using hg i hi
  | succ k =>
    simp only [List.getElem_cons_succ] at hi
    have hk : k < gs.length := by simp at hj; omega
    have h := hgs k hk i hi
    omega

theorem gatesRB_append {base : ℕ} {gs1 gs2 : List Gate}
    (h1 : GatesRB base gs1) (h2 : GatesRB (base + gs1.length) gs2) :
    GatesRB base (gs1 ++ gs2) := by
  intro j hj i hi
  by_cases hlt : j < gs1.length
  · rw [List.getElem_append_left hlt] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := by omega
    rw [List.getElem_append_right hge] at hi
    have hk : j - gs1.length < gs2.length := by simp at hj; omega
    have h := h2 (j - gs1.length) hk i hi
    omega

theorem gatesRB_to_readsBack {n : ℕ} {C : Circuit} (h : GatesRB n C.gates) :
    ReadsBack n C := by
  intro j hj i hi
  have hg : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [hg] at hi
  exact h j hj i hi

-- Or-chain over a list of wires starting from accumulator acc
def orChainAux (curBase acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: rest =>
    let res := orChainAux (curBase + 1) curBase rest
    (⟨.or, [acc, w]⟩ :: res.1, res.2)

theorem orChainAux_len (curBase acc : ℕ) (rest : List ℕ) :
    (orChainAux curBase acc rest).1.length = rest.length := by
  induction rest generalizing curBase acc with
  | nil => rfl
  | cons w rest ih => simp [orChainAux, ih]

theorem orChainAux_out_lt (curBase acc : ℕ) (rest : List ℕ) (hacc : acc < curBase) :
    (orChainAux curBase acc rest).2 < curBase + rest.length := by
  induction rest generalizing curBase acc with
  | nil => simpa [orChainAux] using hacc
  | cons w rest ih =>
    simp only [orChainAux, List.length_cons]
    have h := ih (curBase + 1) curBase (by omega)
    omega

theorem orChainAux_ok (curBase acc : ℕ) (rest : List ℕ) :
    ∀ g ∈ (orChainAux curBase acc rest).1, GateOK g := by
  induction rest generalizing curBase acc with
  | nil => simp [orChainAux]
  | cons w rest ih =>
    intro g hg
    simp only [orChainAux, List.mem_cons] at hg
    rcases hg with rfl | hmem
    · exact ⟨by simp, by simp⟩
    · exact ih (curBase + 1) curBase g hmem

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem orChainAux_rb (curBase acc : ℕ) (rest : List ℕ)
    (hacc : acc < curBase) (hrest : ∀ w ∈ rest, w < curBase) :
    GatesRB curBase (orChainAux curBase acc rest).1 := by
  induction rest generalizing curBase acc with
  | nil => exact gatesRB_nil curBase
  | cons w rest ih =>
    simp only [orChainAux]
    apply gatesRB_cons
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hacc
      · exact hrest i (by simp)
    · apply ih (curBase + 1) curBase (by omega)
      intro u hu
      have := hrest u (by simp [hu])
      omega

theorem orChainAux_eval (curBase acc : ℕ) (rest : List ℕ) (vec : List Bool)
    (hlen : vec.length = curBase) (hacc : acc < curBase) (hrest : ∀ w ∈ rest, w < curBase) :
    ((orChainAux curBase acc rest).1.foldl step vec).getD (orChainAux curBase acc rest).2 false =
      (vec.getD acc false || rest.any (fun w => vec.getD w false)) := by
  induction rest generalizing curBase acc vec with
  | nil => simp [orChainAux]
  | cons w rest ih =>
    simp only [orChainAux, List.foldl_cons, List.any_cons]
    set g : Gate := ⟨.or, [acc, w]⟩
    set vec' := step vec g
    have hlen' : vec'.length = curBase + 1 := by simp [vec', step_length, hlen]
    have hrest' : ∀ u ∈ rest, u < curBase + 1 := fun u hu => by
      have := hrest u (by simp [hu]); omega
    rw [ih (curBase + 1) curBase vec' hlen' (by omega) hrest']
    have hnew : vec'.getD curBase false = (vec.getD acc false || vec.getD w false) := by
      have h0 : vec'.getD vec.length false = g.op.eval (g.inputs.map fun i => vec.getD i false) :=
        step_getD_last vec g
      rw [hlen] at h0
      simpa [vec', g, GateOp.eval] using h0
    have hany : rest.any (fun u => vec'.getD u false) = rest.any (fun u => vec.getD u false) := by
      apply any_congr_mem
      intro u hu
      have hult : u < vec.length := by rw [hlen]; exact hrest u (by simp [hu])
      exact step_getD_lt vec g hult
    rw [hnew, hany, Bool.or_assoc]

-- Build one wire per nonempty group of wires
def buildGroups (base : ℕ) : List (List ℕ) → List Gate × List ℕ
  | [] => ([], [])
  | [] :: rest => buildGroups base rest
  | (w0 :: ws) :: rest =>
    let r1 := orChainAux base w0 ws
    let r2 := buildGroups (base + r1.1.length) rest
    (r1.1 ++ r2.1, r1.2 :: r2.2)

theorem buildGroups_len (base : ℕ) (groups : List (List ℕ))
    (hne : ∀ grp ∈ groups, grp ≠ []) :
    (buildGroups base groups).1.length = (groups.map (fun grp => grp.length - 1)).sum := by
  induction groups generalizing base with
  | nil => rfl
  | cons grp rest ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] (by simp))
    | cons w0 ws =>
      simp only [buildGroups, List.length_append, orChainAux_len, List.map_cons,
        List.sum_cons, List.length_cons, Nat.add_sub_cancel]
      rw [ih (base + ws.length) (fun g hg => hne g (by simp [hg]))]

theorem buildGroups_outs_len (base : ℕ) (groups : List (List ℕ))
    (hne : ∀ grp ∈ groups, grp ≠ []) :
    (buildGroups base groups).2.length = groups.length := by
  induction groups generalizing base with
  | nil => rfl
  | cons grp rest ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] (by simp))
    | cons w0 ws =>
      simp only [buildGroups, List.length_cons]
      rw [ih (base + (orChainAux base w0 ws).1.length) (fun g hg => hne g (by simp [hg]))]

theorem buildGroups_outs_lt (base : ℕ) (groups : List (List ℕ))
    (hne : ∀ grp ∈ groups, grp ≠ [])
    (hlt : ∀ grp ∈ groups, ∀ w ∈ grp, w < base) :
    ∀ o ∈ (buildGroups base groups).2, o < base + (buildGroups base groups).1.length := by
  induction groups generalizing base with
  | nil => simp [buildGroups]
  | cons grp rest ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] (by simp))
    | cons w0 ws =>
      intro o ho
      simp only [buildGroups, List.mem_cons, List.length_append] at ho ⊢
      have hw0 : w0 < base := hlt (w0 :: ws) (by simp) w0 (by simp)
      rcases ho with rfl | hmem
      · have h1 := orChainAux_out_lt base w0 ws hw0
        rw [orChainAux_len]
        omega
      · have hne' : ∀ g ∈ rest, g ≠ [] := fun g hg => hne g (by simp [hg])
        have hlt' : ∀ g ∈ rest, ∀ w ∈ g, w < base + (orChainAux base w0 ws).1.length := by
          intro g hg w hw
          have := hlt g (by simp [hg]) w hw
          omega
        have h2 := ih (base + (orChainAux base w0 ws).1.length) hne' hlt' o hmem
        omega

theorem buildGroups_ok (base : ℕ) (groups : List (List ℕ))
    (hne : ∀ grp ∈ groups, grp ≠ []) :
    ∀ g ∈ (buildGroups base groups).1, GateOK g := by
  induction groups generalizing base with
  | nil => simp [buildGroups]
  | cons grp rest ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] (by simp))
    | cons w0 ws =>
      intro g hg
      simp only [buildGroups, List.mem_append] at hg
      rcases hg with h1 | h2
      · exact orChainAux_ok base w0 ws g h1
      · exact ih (base + (orChainAux base w0 ws).1.length) (fun g hg => hne g (by simp [hg])) g h2

theorem buildGroups_rb (base : ℕ) (groups : List (List ℕ))
    (hne : ∀ grp ∈ groups, grp ≠ [])
    (hlt : ∀ grp ∈ groups, ∀ w ∈ grp, w < base) :
    GatesRB base (buildGroups base groups).1 := by
  induction groups generalizing base with
  | nil => exact gatesRB_nil base
  | cons grp rest ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] (by simp))
    | cons w0 ws =>
      simp only [buildGroups]
      apply gatesRB_append
      · exact orChainAux_rb base w0 ws (hlt (w0 :: ws) (by simp) w0 (by simp))
          (fun w hw => hlt (w0 :: ws) (by simp) w (by simp [hw]))
      · apply ih (base + (orChainAux base w0 ws).1.length)
          (fun g hg => hne g (by simp [hg]))
        intro g hg w hw
        have := hlt g (by simp [hg]) w hw
        omega

theorem buildGroups_eval (base : ℕ) (groups : List (List ℕ)) (vec : List Bool)
    (hlen : vec.length = base)
    (hne : ∀ grp ∈ groups, grp ≠ [])
    (hlt : ∀ grp ∈ groups, ∀ w ∈ grp, w < base) :
    (buildGroups base groups).2.map (fun o => ((buildGroups base groups).1.foldl step vec).getD o false) =
      groups.map (fun grp => grp.any (fun w => vec.getD w false)) := by
  induction groups generalizing base vec with
  | nil => rfl
  | cons grp rest ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] (by simp))
    | cons w0 ws =>
      simp only [buildGroups, List.map_cons, List.foldl_append]
      set r1 := orChainAux base w0 ws
      set vec1 := r1.1.foldl step vec
      have hlen1 : vec1.length = base + r1.1.length := by
        simp [vec1, foldl_length, hlen]
      have hw0 : w0 < base := hlt (w0 :: ws) (by simp) w0 (by simp)
      have hws : ∀ w ∈ ws, w < base := fun w hw => hlt (w0 :: ws) (by simp) w (by simp [hw])
      have hout1 : r1.2 < vec1.length := by
        rw [hlen1, orChainAux_len]
        exact orChainAux_out_lt base w0 ws hw0
      have hhead : ((buildGroups (base + r1.1.length) rest).1.foldl step vec1).getD r1.2 false =
          (w0 :: ws).any (fun w => vec.getD w false) := by
        rw [foldl_getD_lt _ vec1 hout1]
        have hev := orChainAux_eval base w0 ws vec hlen hw0 hws
        simpa [r1, vec1, List.any_cons] using hev
      have hne' : ∀ g ∈ rest, g ≠ [] := fun g hg => hne g (by simp [hg])
      have hlt' : ∀ g ∈ rest, ∀ w ∈ g, w < base + r1.1.length := fun g hg w hw => by
        have := hlt g (by simp [hg]) w hw; omega
      have htail := ih (base + r1.1.length) vec1 hlen1 hne' hlt'
      have htail2 : rest.map (fun g => g.any (fun w => vec1.getD w false)) =
          rest.map (fun g => g.any (fun w => vec.getD w false)) := by
        apply List.map_congr_left
        intro g hg
        apply any_congr_mem
        intro w hw
        have hwlt : w < vec.length := by rw [hlen]; exact hlt g (by simp [hg]) w hw
        exact foldl_getD_lt r1.1 vec hwlt
      rw [hhead, htail, htail2]

-- Threshold-2 circuit on m >= 2 wires in exactly 3*m - 5 gates
def atLeastTwoStep (curBase oPrev tPrev : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], tPrev)
  | [w] =>
    ([⟨.and, [oPrev, w]⟩, ⟨.or, [tPrev, curBase]⟩], curBase + 1)
  | w :: w' :: rest =>
    let res := atLeastTwoStep (curBase + 3) (curBase + 2) (curBase + 1) (w' :: rest)
    (⟨.and, [oPrev, w]⟩ :: ⟨.or, [tPrev, curBase]⟩ :: ⟨.or, [oPrev, w]⟩ :: res.1, res.2)

def atLeastTwo (base : ℕ) : List ℕ → List Gate × ℕ
  | [w0, w1] => ([⟨.and, [w0, w1]⟩], base)
  | w0 :: w1 :: w2 :: rest =>
    let res := atLeastTwoStep (base + 2) (base + 1) base (w2 :: rest)
    (⟨.and, [w0, w1]⟩ :: ⟨.or, [w0, w1]⟩ :: res.1, res.2)
  | _ => ([], 0)

theorem atLeastTwoStep_len (curBase oPrev tPrev : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (atLeastTwoStep curBase oPrev tPrev ws).1.length = 3 * ws.length - 1 := by
  induction ws generalizing curBase oPrev tPrev with
  | nil => exact absurd rfl hne
  | cons w tail ih =>
    cases tail with
    | nil => simp [atLeastTwoStep]
    | cons w' rest =>
      simp only [atLeastTwoStep, List.length_cons]
      have h := ih (curBase + 3) (curBase + 2) (curBase + 1) (by simp)
      simp only [List.length_cons] at h
      omega

theorem atLeastTwo_len (base : ℕ) (ws : List ℕ) (h2 : 2 ≤ ws.length) :
    (atLeastTwo base ws).1.length = 3 * ws.length - 5 := by
  match ws with
  | [] => simp at h2
  | [_] => simp at h2
  | [_, _] => simp [atLeastTwo]
  | _ :: _ :: w2 :: rest =>
    simp only [atLeastTwo, List.length_cons]
    have h := atLeastTwoStep_len (base + 2) (base + 1) base (w2 :: rest) (by simp)
    simp only [List.length_cons] at h
    omega

theorem atLeastTwoStep_ok (curBase oPrev tPrev : ℕ) (ws : List ℕ) :
    ∀ g ∈ (atLeastTwoStep curBase oPrev tPrev ws).1, GateOK g := by
  induction ws generalizing curBase oPrev tPrev with
  | nil => simp [atLeastTwoStep]
  | cons w tail ih =>
    cases tail with
    | nil =>
      intro g hg
      simp only [atLeastTwoStep, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> exact ⟨by simp, by simp⟩
    | cons w' rest =>
      intro g hg
      simp only [atLeastTwoStep, List.mem_cons] at hg
      rcases hg with rfl | rfl | rfl | hmem
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact ih (curBase + 3) (curBase + 2) (curBase + 1) g hmem

theorem atLeastTwo_ok (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ (atLeastTwo base ws).1, GateOK g := by
  match ws with
  | [] => simp [atLeastTwo]
  | [_] => simp [atLeastTwo]
  | [w0, w1] =>
    intro g hg
    simp only [atLeastTwo, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl
    exact ⟨by simp, by simp⟩
  | w0 :: w1 :: w2 :: rest =>
    intro g hg
    simp only [atLeastTwo, List.mem_cons] at hg
    rcases hg with rfl | rfl | hmem
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact atLeastTwoStep_ok (base + 2) (base + 1) base (w2 :: rest) g hmem

theorem atLeastTwoStep_rb (curBase oPrev tPrev : ℕ) (ws : List ℕ)
    (ho : oPrev < curBase) (ht : tPrev < curBase) (hws : ∀ w ∈ ws, w < curBase) :
    GatesRB curBase (atLeastTwoStep curBase oPrev tPrev ws).1 := by
  induction ws generalizing curBase oPrev tPrev with
  | nil => exact gatesRB_nil curBase
  | cons w tail ih =>
    have hw : w < curBase := hws w (by simp)
    cases tail with
    | nil =>
      simp only [atLeastTwoStep]
      apply gatesRB_cons
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
      · apply gatesRB_cons
        · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
        · exact gatesRB_nil _
    | cons w' rest =>
      simp only [atLeastTwoStep]
      apply gatesRB_cons
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
      · apply gatesRB_cons
        · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
        · apply gatesRB_cons
          · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
          · have hrb := ih (curBase + 3) (curBase + 2) (curBase + 1) (by omega) (by omega)
              (fun u hu => by have := hws u (by simp [hu]); omega)
            have heq : curBase + 1 + 1 + 1 = curBase + 3 := by omega
            simpa [heq] using hrb

theorem atLeastTwo_rb (base : ℕ) (ws : List ℕ) (hws : ∀ w ∈ ws, w < base) :
    GatesRB base (atLeastTwo base ws).1 := by
  match ws with
  | [] => exact gatesRB_nil base
  | [_] => exact gatesRB_nil base
  | [w0, w1] =>
    simp only [atLeastTwo]
    apply gatesRB_cons
    · intro i hi; simp at hi
      rcases hi with rfl | rfl
      · exact hws i (by simp)
      · exact hws i (by simp)
    · exact gatesRB_nil _
  | w0 :: w1 :: w2 :: rest =>
    simp only [atLeastTwo]
    apply gatesRB_cons
    · intro i hi; simp at hi
      rcases hi with rfl | rfl
      · exact hws i (by simp)
      · exact hws i (by simp)
    · apply gatesRB_cons
      · intro i hi; simp at hi
        rcases hi with rfl | rfl
        · have := hws i (by simp); omega
        · have := hws i (by simp); omega
      · have hrb := atLeastTwoStep_rb (base + 2) (base + 1) base (w2 :: rest)
          (by omega) (by omega) (fun u hu => by have := hws u (by simp [hu]); omega)
        have heq : base + 1 + 1 = base + 2 := by omega
        simpa [heq] using hrb

def stepSpec (o t : Bool) : List Bool → Bool
  | [] => t
  | b :: bs => stepSpec (o || b) (t || (o && b)) bs

theorem any_id_iff_count_pos (bs : List Bool) :
    bs.any id = decide (1 ≤ bs.count true) := by
  cases h : bs.any id
  · have hc : bs.count true = 0 := by
      rw [List.count_eq_zero]
      intro hmem
      have : bs.any id = true := List.any_eq_true.mpr ⟨true, hmem, rfl⟩
      simp [h] at this
    simp [hc]
  · obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp h
    have hmem : true ∈ bs := by rw [← hxt]; exact hx
    have hc : 0 < bs.count true := List.count_pos_iff.mpr hmem
    simp [show 1 ≤ bs.count true by omega]

theorem stepSpec_eq (o t : Bool) (bs : List Bool) :
    stepSpec o t bs = (t || (o && bs.any id) || decide (2 ≤ bs.count true)) := by
  induction bs generalizing o t with
  | nil => simp [stepSpec]
  | cons b bs ih =>
    simp only [stepSpec, ih, List.any_cons, List.count_cons, id_eq]
    cases b with
    | false =>
      simp
    | true =>
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [any_id_iff_count_pos bs]
      by_cases h1 : 1 ≤ bs.count true <;> by_cases h2 : 2 ≤ bs.count true <;>
        cases o <;> cases t <;> (simp [h1, h2]; try omega)

theorem atLeastTwoStep_eval (curBase oPrev tPrev : ℕ) (ws : List ℕ) (vec : List Bool)
    (hlen : vec.length = curBase) (ho : oPrev < curBase) (ht : tPrev < curBase)
    (hws : ∀ w ∈ ws, w < curBase) :
    ((atLeastTwoStep curBase oPrev tPrev ws).1.foldl step vec).getD
      (atLeastTwoStep curBase oPrev tPrev ws).2 false =
      stepSpec (vec.getD oPrev false) (vec.getD tPrev false) (ws.map fun w => vec.getD w false) := by
  induction ws generalizing curBase oPrev tPrev vec with
  | nil => simp [atLeastTwoStep, stepSpec]
  | cons w tail ih =>
    have hw : w < curBase := hws w (by simp)
    cases tail with
    | nil =>
      simp only [atLeastTwoStep, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
        stepSpec]
      set gA : Gate := ⟨.and, [oPrev, w]⟩
      set gT : Gate := ⟨.or, [tPrev, curBase]⟩
      set v1 := step vec gA
      set v2 := step v1 gT
      have hv1len : v1.length = curBase + 1 := by simp [v1, step_length, hlen]
      have hv1A : v1.getD curBase false = (vec.getD oPrev false && vec.getD w false) := by
        have h := step_getD_last vec gA
        rw [hlen] at h
        simpa [gA, GateOp.eval] using h
      have hv1T : v1.getD tPrev false = vec.getD tPrev false :=
        step_getD_lt vec gA (by omega)
      have hv2T : v2.getD (curBase + 1) false = (v1.getD tPrev false || v1.getD curBase false) := by
        have h := step_getD_last v1 gT
        rw [hv1len] at h
        simpa [gT, GateOp.eval] using h
      rw [hv2T, hv1T, hv1A]
    | cons w' rest =>
      simp only [atLeastTwoStep, List.foldl_cons, List.map_cons, stepSpec]
      set gA : Gate := ⟨.and, [oPrev, w]⟩
      set gT : Gate := ⟨.or, [tPrev, curBase]⟩
      set gO : Gate := ⟨.or, [oPrev, w]⟩
      set v1 := step vec gA
      set v2 := step v1 gT
      set v3 := step v2 gO
      have hv1len : v1.length = curBase + 1 := by simp [v1, step_length, hlen]
      have hv2len : v2.length = curBase + 2 := by simp [v2, step_length, hv1len]
      have hv3len : v3.length = curBase + 3 := by simp [v3, step_length, hv2len]
      have hrest : ∀ u ∈ w' :: rest, u < curBase + 3 := fun u hu => by
        have := hws u (by simp [hu]); omega
      rw [ih (curBase + 3) (curBase + 2) (curBase + 1) v3 hv3len (by omega) (by omega) hrest]
      have hv1A : v1.getD curBase false = (vec.getD oPrev false && vec.getD w false) := by
        have h := step_getD_last vec gA; rw [hlen] at h; simpa [gA, GateOp.eval] using h
      have hv1T : v1.getD tPrev false = vec.getD tPrev false := step_getD_lt vec gA (by omega)
      have hv1O : v1.getD oPrev false = vec.getD oPrev false := step_getD_lt vec gA (by omega)
      have hv1w : v1.getD w false = vec.getD w false := step_getD_lt vec gA (by omega)
      have hv2T : v2.getD (curBase + 1) false = (vec.getD tPrev false || (vec.getD oPrev false && vec.getD w false)) := by
        have h := step_getD_last v1 gT; rw [hv1len] at h
        simp only [gT, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false] at h
        rw [hv1T, hv1A] at h
        exact h
      have hv2O : v2.getD oPrev false = vec.getD oPrev false := by
        rw [step_getD_lt v1 gT (by omega), hv1O]
      have hv2w : v2.getD w false = vec.getD w false := by
        rw [step_getD_lt v1 gT (by omega), hv1w]
      have hv3T : v3.getD (curBase + 1) false = (vec.getD tPrev false || (vec.getD oPrev false && vec.getD w false)) := by
        rw [step_getD_lt v2 gO (by omega), hv2T]
      have hv3O : v3.getD (curBase + 2) false = (vec.getD oPrev false || vec.getD w false) := by
        have h := step_getD_last v2 gO; rw [hv2len] at h
        simp only [gO, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false] at h
        rw [hv2O, hv2w] at h
        exact h
      have hmap : (w' :: rest).map (fun u => v3.getD u false) = (w' :: rest).map (fun u => vec.getD u false) := by
        apply List.map_congr_left
        intro u hu
        have hu0 : u < curBase := hws u (by simp [hu])
        rw [step_getD_lt v2 gO (by omega), step_getD_lt v1 gT (by omega), step_getD_lt vec gA (by omega)]
      rw [hv3O, hv3T, hmap]
      simp [stepSpec]

theorem atLeastTwo_eval (base : ℕ) (ws : List ℕ) (vec : List Bool)
    (hlen : vec.length = base) (h2 : 2 ≤ ws.length) (hws : ∀ w ∈ ws, w < base) :
    ((atLeastTwo base ws).1.foldl step vec).getD (atLeastTwo base ws).2 false =
      decide (2 ≤ (ws.map fun w => vec.getD w false).count true) := by
  match ws with
  | [] => simp at h2
  | [_] => simp at h2
  | [w0, w1] =>
    simp only [atLeastTwo, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
    set g : Gate := ⟨.and, [w0, w1]⟩
    have h := step_getD_last vec g
    rw [hlen] at h
    have hval : (step vec g).getD base false = (vec.getD w0 false && vec.getD w1 false) := by
      simpa [g, GateOp.eval] using h
    rw [hval]
    cases vec.getD w0 false <;> cases vec.getD w1 false <;> decide
  | w0 :: w1 :: w2 :: rest =>
    simp only [atLeastTwo, List.foldl_cons]
    have hw0 : w0 < base := hws w0 (by simp)
    have hw1 : w1 < base := hws w1 (by simp)
    set gT1 : Gate := ⟨.and, [w0, w1]⟩
    set gO1 : Gate := ⟨.or, [w0, w1]⟩
    set v1 := step vec gT1
    set v2 := step v1 gO1
    have hv1len : v1.length = base + 1 := by simp [v1, step_length, hlen]
    have hv2len : v2.length = base + 2 := by simp [v2, step_length, hv1len]
    have hrest : ∀ u ∈ w2 :: rest, u < base + 2 := fun u hu => by
      have := hws u (by simp [hu]); omega
    rw [atLeastTwoStep_eval (base + 2) (base + 1) base (w2 :: rest) v2 hv2len (by omega) (by omega) hrest]
    have hv1T : v1.getD base false = (vec.getD w0 false && vec.getD w1 false) := by
      have h := step_getD_last vec gT1; rw [hlen] at h; simpa [gT1, GateOp.eval] using h
    have hv2T : v2.getD base false = (vec.getD w0 false && vec.getD w1 false) := by
      rw [step_getD_lt v1 gO1 (by omega), hv1T]
    have hv2O : v2.getD (base + 1) false = (vec.getD w0 false || vec.getD w1 false) := by
      have h := step_getD_last v1 gO1; rw [hv1len] at h
      have h0 : v1.getD w0 false = vec.getD w0 false := step_getD_lt vec gT1 (by omega)
      have h1 : v1.getD w1 false = vec.getD w1 false := step_getD_lt vec gT1 (by omega)
      simp only [gO1, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at h
      rw [h0, h1] at h
      exact h
    have hmap : (w2 :: rest).map (fun u => v2.getD u false) = (w2 :: rest).map (fun u => vec.getD u false) := by
      apply List.map_congr_left
      intro u hu
      have hu0 : u < base := hws u (by simp [hu])
      rw [step_getD_lt v1 gO1 (by omega), step_getD_lt vec gT1 (by omega)]
    rw [hv2O, hv2T, hmap, stepSpec_eq]
    set bs := (w2 :: rest).map (fun u => vec.getD u false)
    have hcnt : ((w0 :: w1 :: w2 :: rest).map fun w => vec.getD w false).count true =
        (if vec.getD w0 false then 1 else 0) + (if vec.getD w1 false then 1 else 0) + bs.count true := by
      simp [bs, List.count_cons]; omega
    rw [hcnt, any_id_iff_count_pos bs]
    cases vec.getD w0 false <;> cases vec.getD w1 false <;> by_cases h1 : 1 ≤ bs.count true <;>
      by_cases h2c : 2 ≤ bs.count true <;> simp [h1, h2c] <;> omega

-- Class wires construction
def classWires (r c m : ℕ) (κr : Fin r → Fin m) (κc : Fin c → Fin m) (K : Fin m) : List ℕ :=
  ((List.finRange r).filter (fun u => decide (κr u = K))).map (fun u => u.val) ++
  ((List.finRange c).filter (fun v => decide (κc v = K))).map (fun v => r + v.val)

theorem oneEach_len {r c : ℕ} (u : Fin r) (v : Fin c) :
    (oneEach u v).length = r + c := by
  simp [oneEach]

theorem oneEach_getD_left {r c : ℕ} (u i : Fin r) (v : Fin c) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  have hlt : i.val < (List.ofFn (fun i : Fin r => decide (i = u))).length := by simp
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

theorem oneEach_getD_right {r c : ℕ} (u : Fin r) (v j : Fin c) :
    (oneEach u v).getD (r + j.val) false = decide (j = v) := by
  simp [oneEach, List.getD_eq_getElem?_getD]

theorem classWires_nonempty {r c m : ℕ} (κr : Fin r → Fin m) (κc : Fin c → Fin m)
    (hsurj : ∀ K : Fin m, (∃ u, κr u = K) ∧ (∃ v, κc v = K)) (K : Fin m) :
    classWires r c m κr κc K ≠ [] := by
  obtain ⟨⟨u, hu⟩, _⟩ := hsurj K
  intro h
  have hmem : u.val ∈ classWires r c m κr κc K := by
    simp only [classWires, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, decide_eq_true_eq]
    exact Or.inl ⟨u, hu, rfl⟩
  rw [h] at hmem
  simp at hmem

theorem classWires_lt {r c m : ℕ} (κr : Fin r → Fin m) (κc : Fin c → Fin m) (K : Fin m) :
    ∀ w ∈ classWires r c m κr κc K, w < r + c := by
  intro w hw
  simp only [classWires, List.mem_append, List.mem_map, List.mem_filter] at hw
  rcases hw with ⟨u, _, rfl⟩ | ⟨v, _, rfl⟩
  · omega
  · omega

theorem classWires_any {r c m : ℕ} (κr : Fin r → Fin m) (κc : Fin c → Fin m)
    (u : Fin r) (v : Fin c) (K : Fin m) :
    (classWires r c m κr κc K).any (fun w => (oneEach u v).getD w false) =
      decide (κr u = K ∨ κc v = K) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, hget⟩
    simp only [classWires, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and, decide_eq_true_eq] at hw
    rcases hw with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [oneEach_getD_left, decide_eq_true_eq] at hget
      exact Or.inl (hget ▸ hi)
    · rw [oneEach_getD_right, decide_eq_true_eq] at hget
      exact Or.inr (hget ▸ hj)
  · rintro (hu | hv)
    · refine ⟨u.val, ?_, ?_⟩
      · simp only [classWires, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
          true_and, decide_eq_true_eq]
        exact Or.inl ⟨u, hu, rfl⟩
      · rw [oneEach_getD_left]; simp
    · refine ⟨r + v.val, ?_, ?_⟩
      · simp only [classWires, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
          true_and, decide_eq_true_eq]
        exact Or.inr ⟨v, hv, rfl⟩
      · rw [oneEach_getD_right]; simp

theorem sum_filter_finRange {n m : ℕ} (f : Fin n → Fin m) :
    ((List.finRange m).map (fun K => ((List.finRange n).filter (fun i => decide (f i = K))).length)).sum = n := by
  have h1 : ∀ (L : List (Fin n)),
      ((List.finRange m).map (fun K => (L.filter (fun i => decide (f i = K))).length)).sum = L.length := by
    intro L
    induction L with
    | nil =>
      simp
    | cons a as ih =>
      have hstep : ((List.finRange m).map (fun K => ((a :: as).filter (fun i => decide (f i = K))).length)).sum =
          ((List.finRange m).map (fun K => (if f a = K then 1 else 0) + (as.filter (fun i => decide (f i = K))).length)).sum := by
        congr 1
        apply List.map_congr_left
        intro K _
        by_cases h : f a = K <;> simp [h]
        omega
      rw [hstep]
      have hsplit : ∀ (Ks : List (Fin m)),
          (Ks.map (fun K => (if f a = K then 1 else 0) + (as.filter (fun i => decide (f i = K))).length)).sum =
            (Ks.map (fun K => if f a = K then 1 else 0)).sum +
            (Ks.map (fun K => (as.filter (fun i => decide (f i = K))).length)).sum := by
        intro Ks
        induction Ks with
        | nil => simp
        | cons k ks ihk => simp [ihk]; omega
      rw [hsplit, ih]
      have hone : ((List.finRange m).map (fun K => if f a = K then 1 else 0)).sum = 1 := by
        have hnodup : (List.finRange m).Nodup := List.nodup_finRange m
        have hmem : f a ∈ List.finRange m := List.mem_finRange (f a)
        have hsum : ∀ (Ks : List (Fin m)), Ks.Nodup →
            (Ks.map (fun K => if f a = K then 1 else 0)).sum = if f a ∈ Ks then 1 else 0 := by
          intro Ks hnd
          induction Ks with
          | nil => simp
          | cons k ks ihk =>
            rw [List.nodup_cons] at hnd
            rw [List.map_cons, List.sum_cons, ihk hnd.2]
            by_cases h : f a = k
            · subst h; simp [hnd.1]
            · simp [h]
        rw [hsum _ hnodup]
        simp [hmem]
      rw [hone]
      simp [Nat.add_comm]
  simpa using h1 (List.finRange n)

theorem sum_classWires_sub_one {r c m : ℕ} (κr : Fin r → Fin m) (κc : Fin c → Fin m)
    (hsurj : ∀ K : Fin m, (∃ u, κr u = K) ∧ (∃ v, κc v = K)) :
    (((List.finRange m).map (classWires r c m κr κc)).map (fun grp => grp.length - 1)).sum = r + c - m := by
  have hge1 : ∀ K : Fin m, 1 ≤ (classWires r c m κr κc K).length := by
    intro K
    have hne := classWires_nonempty κr κc hsurj K
    cases h : classWires r c m κr κc K
    · exact absurd h hne
    · simp
  have hadd : ∀ (Ks : List (Fin m)),
      (Ks.map (fun K => (classWires r c m κr κc K).length - 1)).sum + Ks.length =
        (Ks.map (fun K => (classWires r c m κr κc K).length)).sum := by
    intro Ks
    induction Ks with
    | nil => simp
    | cons K Ks ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hK := hge1 K
      omega
  have htot : ((List.finRange m).map (fun K => (classWires r c m κr κc K).length)).sum = r + c := by
    have hsplit : ∀ (Ks : List (Fin m)),
        (Ks.map (fun K => (classWires r c m κr κc K).length)).sum =
          (Ks.map (fun K => ((List.finRange r).filter (fun u => decide (κr u = K))).length)).sum +
          (Ks.map (fun K => ((List.finRange c).filter (fun v => decide (κc v = K))).length)).sum := by
      intro Ks
      induction Ks with
      | nil => simp
      | cons K Ks ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        simp only [classWires, List.length_append, List.length_map]
        omega
    rw [hsplit, sum_filter_finRange κr, sum_filter_finRange κc]
  have hfin := hadd (List.finRange m)
  rw [List.length_finRange, htot] at hfin
  rw [List.map_map]
  change ((List.finRange m).map (fun K => (classWires r c m κr κc K).length - 1)).sum = r + c - m
  omega

theorem count_disj_finRange {m : ℕ} (a b : Fin m) :
    decide (2 ≤ ((List.finRange m).map (fun K => decide (a = K ∨ b = K))).count true) =
      decide (a ≠ b) := by
  have hcnt : ∀ (Ks : List (Fin m)), Ks.Nodup →
      (Ks.map (fun K => decide (a = K ∨ b = K))).count true =
        if a = b then (if a ∈ Ks then 1 else 0)
        else (if a ∈ Ks then 1 else 0) + (if b ∈ Ks then 1 else 0) := by
    intro Ks hnd
    induction Ks with
    | nil => simp
    | cons k ks ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.count_cons, ih hnd.2]
      by_cases hab : a = b
      · subst hab
        by_cases hak : a = k
        · subst hak; simp [hnd.1]
        · simp [hak]
      · by_cases hak : a = k
        · subst hak
          have hbk : b ≠ a := Ne.symm hab
          simp [hab, hnd.1, hbk]
          omega
        · by_cases hbk : b = k
          · subst hbk
            simp [hab, hnd.1]
          · simp [hab, hak, hbk]
  rw [hcnt (List.finRange m) (List.nodup_finRange m)]
  simp only [List.mem_finRange, ite_true]
  by_cases hab : a = b <;> simp [hab]

end PEqualNP.Outside.L_meta_25452_aux

open PEqualNP.Outside.L_meta_25452_aux in
theorem PEqualNP.Outside.L_meta_25452 : ∀ (r c m : ℕ) (κr : Fin r → Fin m) (κc : Fin c → Fin m), 2 ≤ m → (∀ K : Fin m, (∃ u, κr u = K) ∧ (∃ v, κc v = K)) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) C ∧ C.size ≤ (r + c - m) + (3 * m - 5) ∧ PEqualNP.Represents.Represents (fun (u : Fin r) (v : Fin c) => decide (κr u ≠ κc v)) C := by
  intro r c m κr κc hm hsurj
  let groups : List (List ℕ) := (List.finRange m).map (classWires r c m κr κc)
  have hne : ∀ grp ∈ groups, grp ≠ [] := by
    intro grp hgrp
    simp only [groups, List.mem_map] at hgrp
    obtain ⟨K, _, rfl⟩ := hgrp
    exact classWires_nonempty κr κc hsurj K
  have hlt : ∀ grp ∈ groups, ∀ w ∈ grp, w < r + c := by
    intro grp hgrp w hw
    simp only [groups, List.mem_map] at hgrp
    obtain ⟨K, _, rfl⟩ := hgrp
    exact classWires_lt κr κc K w hw
  let g1 := buildGroups (r + c) groups
  let base2 := r + c + g1.1.length
  let g2 := atLeastTwo base2 g1.2
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨g1.1 ++ g2.1, g2.2⟩
  have houts_len : g1.2.length = m := by
    have h := buildGroups_outs_len (r + c) groups hne
    simpa [groups] using h
  have houts_lt : ∀ o ∈ g1.2, o < base2 :=
    buildGroups_outs_lt (r + c) groups hne hlt
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_append] at hg
    rcases hg with h1 | h2
    · exact buildGroups_ok (r + c) groups hne g h1
    · exact atLeastTwo_ok base2 g1.2 g h2
  · apply gatesRB_to_readsBack
    exact gatesRB_append (buildGroups_rb (r + c) groups hne hlt)
      (atLeastTwo_rb base2 g1.2 houts_lt)
  · simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append]
    have hl1 : g1.1.length = r + c - m := by
      rw [buildGroups_len (r + c) groups hne]
      exact sum_classWires_sub_one κr κc hsurj
    have hl2 : g2.1.length = 3 * m - 5 := by
      have h := atLeastTwo_len base2 g1.2 (by omega)
      rw [houts_len] at h
      exact h
    omega
  · intro u v
    simp only [C, PEqualNP.CircuitLowerBounds.Circuit.eval, wires_eq_foldl, List.foldl_append]
    set vec1 := g1.1.foldl step (PEqualNP.Represents.oneEach u v)
    have hlen1 : vec1.length = base2 := by
      simp [vec1, base2, foldl_length, oneEach_len]
    rw [atLeastTwo_eval base2 g1.2 vec1 hlen1 (by omega) houts_lt]
    have hev1 := buildGroups_eval (r + c) groups (PEqualNP.Represents.oneEach u v)
      (oneEach_len u v) hne hlt
    rw [hev1]
    have hmap : groups.map (fun grp => grp.any (fun w => (PEqualNP.Represents.oneEach u v).getD w false)) =
        (List.finRange m).map (fun K => decide (κr u = K ∨ κc v = K)) := by
      simp only [groups, List.map_map]
      apply List.map_congr_left
      intro K _
      exact classWires_any κr κc u v K
    rw [hmap]
    exact count_disj_finRange (κr u) (κc v)
