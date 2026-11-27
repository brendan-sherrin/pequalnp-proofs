import PEqualNP.Defs
import PEqualNP.Outside.L_meta_17555

namespace PEqualNP.Outside.L_meta_18739_aux

abbrev W32 := BitVec 32

def initW : List W32 :=
  [(8372227 : W32), (1292189708 : W32), (0 : W32), (1418772528 : W32),
   (42631364 : W32), (202359552 : W32), (52628496 : W32), (676074528 : W32),
   (812654920 : W32), (1132474881 : W32), (2080376962 : W32)]

def GoodList (l : List W32) : Prop :=
  ∀ i : Fin l.length,
    have w : List W32 := initW ++ List.take (↑i) l
    (∃ a ∈ w, ∃ b ∈ w, l.get i = a &&& b ∨ l.get i = a ||| b) ∧
    ∀ a ∈ w, (a ^^^ (16383 : W32)) &&& (l.get i ^^^ (16383 : W32)) ≠ a ^^^ (16383 : W32)

lemma getD_mem_of_zero_mem (l : List W32) (h0 : (0 : W32) ∈ l) (i : ℕ) : l.getD i 0 ∈ l := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · rw [List.getD_eq_default _ _ (Nat.not_lt.mp h)]
    exact h0

lemma goodList_snoc {l : List W32} (hg : GoodList l) {z : W32}
    (hstep : ∃ a ∈ initW ++ l, ∃ b ∈ initW ++ l, z = a &&& b ∨ z = a ||| b)
    (hdom : ∀ a ∈ initW ++ l, (a ^^^ (16383 : W32)) &&& (z ^^^ (16383 : W32)) ≠ a ^^^ (16383 : W32)) :
    GoodList (l ++ [z]) := by
  intro i
  have hi : i.1 < l.length + 1 := by simpa using i.2
  by_cases hlt : i.1 < l.length
  · have hget : (l ++ [z]).get i = l.get ⟨i.1, hlt⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hlt]
    have htake : List.take i.1 (l ++ [z]) = List.take i.1 l := by
      rw [List.take_append_of_le_length (by omega)]
    simpa only [hget, htake] using hg ⟨i.1, hlt⟩
  · have heq : i.1 = l.length := by omega
    have hget : (l ++ [z]).get i = z := by
      simp [List.get_eq_getElem, heq]
    have htake : List.take i.1 (l ++ [z]) = l := by
      rw [heq, List.take_left]
    simpa only [hget, htake] using And.intro hstep hdom

def stepFn (acc : List W32) (op : Fin 32 × Fin 32 × Bool) : List W32 :=
  have x3 : W32 := acc.getD ↑op.1 (0 : W32)
  have x4 : W32 := acc.getD ↑op.2.1 (0 : W32)
  have x5 : W32 := if op.2.2 = Bool.true then x3 ||| x4 else x3 &&& x4
  if (acc.any fun x6 : W32 => (x6 ^^^ (16383 : W32)) &&& (x5 ^^^ (16383 : W32)) == x6 ^^^ (16383 : W32)) = Bool.true
  then acc else acc ++ [x5]

lemma foldl_good (ops : List (Fin 32 × Fin 32 × Bool)) (l : List W32) (hg : GoodList l) :
    ∃ l' : List W32, List.foldl stepFn (initW ++ l) ops = initW ++ l' ∧
      l'.length ≤ l.length + ops.length ∧ GoodList l' := by
  induction ops generalizing l with
  | nil => exact ⟨l, rfl, by simp, hg⟩
  | cons op rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    let x3 : W32 := (initW ++ l).getD ↑op.1 (0 : W32)
    let x4 : W32 := (initW ++ l).getD ↑op.2.1 (0 : W32)
    let x5 : W32 := if op.2.2 = Bool.true then x3 ||| x4 else x3 &&& x4
    by_cases hany : ((initW ++ l).any fun x6 : W32 =>
        (x6 ^^^ (16383 : W32)) &&& (x5 ^^^ (16383 : W32)) == x6 ^^^ (16383 : W32)) = Bool.true
    · have hst : stepFn (initW ++ l) op = initW ++ l := by
        dsimp only [stepFn]
        exact if_pos hany
      rw [hst]
      obtain ⟨l', heq, hlen, hg'⟩ := ih l hg
      exact ⟨l', heq, by omega, hg'⟩
    · have hst : stepFn (initW ++ l) op = initW ++ (l ++ [x5]) := by
        dsimp only [stepFn]
        rw [if_neg hany, List.append_assoc]
      rw [hst]
      have h0 : (0 : W32) ∈ initW ++ l := List.mem_append_left _ (by simp [initW])
      have hx3 : x3 ∈ initW ++ l := getD_mem_of_zero_mem _ h0 _
      have hx4 : x4 ∈ initW ++ l := getD_mem_of_zero_mem _ h0 _
      have hstep : ∃ a ∈ initW ++ l, ∃ b ∈ initW ++ l, x5 = a &&& b ∨ x5 = a ||| b :=
        ⟨x3, hx3, x4, hx4, by cases hb : op.2.2 <;> simp [x5, hb]⟩
      have hdom : ∀ a ∈ initW ++ l, (a ^^^ (16383 : W32)) &&& (x5 ^^^ (16383 : W32)) ≠ a ^^^ (16383 : W32) := by
        intro a ha heq
        apply hany
        rw [List.any_eq_true]
        exact ⟨a, ha, beq_iff_eq.mpr heq⟩
      have hg1 : GoodList (l ++ [x5]) := goodList_snoc hg hstep hdom
      obtain ⟨l', heq, hlen, hg'⟩ := ih (l ++ [x5]) hg1
      refine ⟨l', heq, ?_, hg'⟩
      simp at hlen
      omega

end PEqualNP.Outside.L_meta_18739_aux

open PEqualNP.Outside.L_meta_18739_aux in
theorem PEqualNP.Outside.L_meta_18739 :
    have x1 : List (BitVec (32 : ℕ)) → Fin (32 : ℕ) × Fin (32 : ℕ) × Bool → List (BitVec (32 : ℕ)) := fun (x1 : List (BitVec (32 : ℕ))) (x2 : Fin (32 : ℕ) × Fin (32 : ℕ) × Bool) =>   have x3 : BitVec (32 : ℕ) := x1.getD ↑x2.1 (0 : BitVec (32 : ℕ));   have x4 : BitVec (32 : ℕ) := x1.getD ↑x2.2.1 (0 : BitVec (32 : ℕ));   have x5 : BitVec (32 : ℕ) := if x2.2.2 = Bool.true then x3 ||| x4 else x3 &&& x4;   if (x1.any fun (x6 : BitVec (32 : ℕ)) => (x6 ^^^ (16383 : BitVec (32 : ℕ))) &&& (x5 ^^^ (16383 : BitVec (32 : ℕ))) == x6 ^^^ (16383 : BitVec (32 : ℕ))) = Bool.true then x1 else x1 ++ [x5]; ∀ (x2 : Fin (18 : ℕ) → Fin (32 : ℕ) × Fin (32 : ℕ) × Bool), (16383 : BitVec (32 : ℕ)) ∉ List.foldl x1 [(8372227 : BitVec (32 : ℕ)), (1292189708 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (1418772528 : BitVec (32 : ℕ)), (42631364 : BitVec (32 : ℕ)), (202359552 : BitVec (32 : ℕ)), (52628496 : BitVec (32 : ℕ)), (676074528 : BitVec (32 : ℕ)), (812654920 : BitVec (32 : ℕ)), (1132474881 : BitVec (32 : ℕ)), (2080376962 : BitVec (32 : ℕ))] (List.ofFn x2) := by
  intro x1 x2
  have hg0 : GoodList [] := fun i => Fin.elim0 i
  obtain ⟨l', heq, hlen, hg'⟩ := foldl_good (List.ofFn x2) [] hg0
  simp only [List.length_nil, Nat.zero_add, List.length_ofFn] at hlen
  have hfn : x1 = stepFn := rfl
  have hinit : [(8372227 : BitVec (32 : ℕ)), (1292189708 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (1418772528 : BitVec (32 : ℕ)), (42631364 : BitVec (32 : ℕ)), (202359552 : BitVec (32 : ℕ)), (52628496 : BitVec (32 : ℕ)), (676074528 : BitVec (32 : ℕ)), (812654920 : BitVec (32 : ℕ)), (1132474881 : BitVec (32 : ℕ)), (2080376962 : BitVec (32 : ℕ))] = initW ++ [] := by
    simp [initW]
  rw [hfn, hinit, heq]
  exact PEqualNP.Outside.L_meta_17555 l' hlen hg'
