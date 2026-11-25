import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.Distinctness
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Hard
import Cslib.Computability.Circuit.Complexity
import Cslib.Computability.Circuit.Full
import Cslib.Computability.Circuit.Boolean.Complexity
import Complexity.Computability.Circuit.Boolean.ElementDistinctness

/-!
# A superlinear Boolean circuit lower bound for element distinctness

We translate fan-in-two Boolean circuits over the full binary basis into the trivalent bit
networks `Net` of the OpenAI development, and combine the translation with its theorem
`BatchDescent.manyList` (the formal version of Theorem 2.2 of
"The matrix multiplication exponent is nine fourths").
-/

namespace CircuitLowerBound

open OAI.LinearAlgebra.MatrixExponent Filter

/-! ## Boolean circuits -/

/-- A straight-line Boolean circuit on `n` inputs. Node `i < n` is input `i`; node `n + k` is
gate `k`, which applies an arbitrary binary Boolean function to two earlier nodes. -/
structure Circuit (n : ℕ) where
  size : ℕ
  op : Fin size → Bool → Bool → Bool
  src₁ : (k : Fin size) → Fin (n + k)
  src₂ : (k : Fin size) → Fin (n + k)
  out : Fin (n + size)

namespace Circuit

variable {n : ℕ} (C : Circuit n)

/-- The value of node `i` on input `x`. -/
def val (x : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then x ⟨i, h⟩
  else if h' : i - n < C.size then
    C.op ⟨i - n, h'⟩ (val x (C.src₁ ⟨i - n, h'⟩)) (val x (C.src₂ ⟨i - n, h'⟩))
  else false
termination_by i
decreasing_by
  · have := (C.src₁ ⟨i - n, h'⟩).isLt
    simp only [Fin.val_mk] at this
    omega
  · have := (C.src₂ ⟨i - n, h'⟩).isLt
    simp only [Fin.val_mk] at this
    omega

/-- The output of the circuit. -/
def eval (x : Fin n → Bool) : Bool := C.val x C.out

/-- A source of gate `k`, as a node of the whole circuit. -/
def src (k : Fin C.size) (b : Bool) : Fin (n + C.size) :=
  Fin.castLE (by have := k.isLt; omega) (if b then C.src₂ k else C.src₁ k)

theorem src_lt (k : Fin C.size) (b : Bool) : (C.src k b : ℕ) < n + k := by
  unfold src
  cases b <;> simp

/-- Node values determined by the inputs `x` and a guess `g` for the gate values. -/
def node (x : Fin n → Bool) (g : Fin C.size → Bool) (j : Fin (n + C.size)) : Bool :=
  if h : (j : ℕ) < n then x ⟨j, h⟩ else g ⟨j - n, by have := j.isLt; omega⟩

/-- `g` is a consistent assignment of gate values. -/
def Consistent (x : Fin n → Bool) (g : Fin C.size → Bool) : Prop :=
  ∀ k, g k = C.op k (C.node x g (C.src k false)) (C.node x g (C.src k true))

/-- The true gate values. -/
def gateVal (x : Fin n → Bool) (k : Fin C.size) : Bool := C.val x (n + k)

theorem val_gate (x : Fin n → Bool) (k : Fin C.size) :
    C.val x (n + k) = C.op k (C.val x (C.src k false)) (C.val x (C.src k true)) := by
  rw [val]
  have h1 : ¬ (n + (k : ℕ) < n) := by omega
  have h2 : n + (k : ℕ) - n < C.size := by have := k.isLt; omega
  rw [dite_eq_right h1, dite_eq_left h2]
  have hk : (⟨n + (k : ℕ) - n, h2⟩ : Fin C.size) = k := Fin.ext (by simp)
  rw [hk]
  simp [src]

theorem node_eq_val {x : Fin n → Bool} {g : Fin C.size → Bool} (hg : C.Consistent x g) :
    ∀ j : Fin (n + C.size), C.node x g j = C.val x j := by
  suffices ∀ i (j : Fin (n + C.size)), (j : ℕ) = i → C.node x g j = C.val x j from
    fun j => this j j rfl
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hj
    by_cases h : (j : ℕ) < n
    · simp [node, h, val]
    · set k : Fin C.size := ⟨j - n, by have := j.isLt; omega⟩ with hkdef
      have hjk : (j : ℕ) = n + k := by simp [hkdef]; omega
      have hnode : C.node x g j = g k := by simp [node, h, hkdef]
      rw [hnode, hg k, hjk, val_gate]
      congr 1
      · exact ih _ (by have := C.src_lt k false; omega) _ rfl
      · exact ih _ (by have := C.src_lt k true; omega) _ rfl

theorem consistent_gateVal (x : Fin n → Bool) : C.Consistent x (C.gateVal x) := by
  have hn : ∀ j : Fin (n + C.size), C.node x (C.gateVal x) j = C.val x j := by
    intro j
    by_cases h : (j : ℕ) < n
    · simp [node, h, val]
    · simp only [node, h, dite_false, gateVal]
      congr 1
      omega
  intro k
  rw [hn, hn]
  exact C.val_gate x k

theorem consistent_iff (x : Fin n → Bool) (g : Fin C.size → Bool) :
    C.Consistent x g ↔ g = C.gateVal x := by
  constructor
  · intro hg
    funext k
    have := C.node_eq_val hg ⟨n + k, by have := k.isLt; omega⟩
    simpa [node, gateVal] using this
  · rintro rfl
    exact C.consistent_gateVal x

end Circuit

/-! ## Encodings of bit vectors as wires -/

/-- Read a word as a vector. -/
def wget : (s : ℕ) → Val (word s) → Fin s → Bool
  | 0, _, i => i.elim0
  | s + 1, z, i => Fin.cases z.1 (wget s z.2) i

/-- Write a vector as a word. -/
def wenc : (s : ℕ) → (Fin s → Bool) → Val (word s)
  | 0, _ => ()
  | s + 1, g => (g 0, wenc s (fun i => g i.succ))

theorem wget_wenc : ∀ (s : ℕ) (g : Fin s → Bool), wget s (wenc s g) = g
  | 0, g => funext fun i => i.elim0
  | s + 1, g => by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [wget, wenc, wget_wenc s]

theorem wenc_wget : ∀ (s : ℕ) (z : Val (word s)), wenc s (wget s z) = z
  | 0, _ => rfl
  | s + 1, z => by
    simp only [wenc, wget, Fin.cases_zero, Fin.cases_succ]
    rw [show (fun i : Fin s => wget s z.2 i) = wget s z.2 from rfl, wenc_wget s z.2]

/-- The slot of a word holding entry `i`. -/
def wslot : (s : ℕ) → Fin s → slots (word s)
  | 0, i => i.elim0
  | s + 1, i => Fin.cases (.inl ()) (fun j => .inr (wslot s j)) i

theorem bits_wslot : ∀ (s : ℕ) (z : Val (word s)) (i : Fin s),
    bits (word s) z (wslot s i) = wget s z i
  | 0, _, i => i.elim0
  | s + 1, z, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [wslot, wget, Fin.cases_succ]
      exact bits_wslot s z.2 j

/-- Gate inputs: a pair of bits per gate. -/
abbrev gw : ℕ → Wire
  | 0 => .unit
  | s + 1 => .pair (.pair .bit .bit) (gw s)

/-- Read the two inputs of gate `i`. -/
def gget : (s : ℕ) → Val (gw s) → Fin s → Bool → Bool
  | 0, _, i, _ => i.elim0
  | s + 1, z, i, b => Fin.cases (if b then z.1.2 else z.1.1) (fun j => gget s z.2 j b) i

/-- Which gate and which input a slot of `gw s` belongs to. -/
def gidx : (s : ℕ) → slots (gw s) → Fin s × Bool
  | 0, t => t.elim
  | _ + 1, .inl (.inl ()) => (0, false)
  | _ + 1, .inl (.inr ()) => (0, true)
  | s + 1, .inr t => ((gidx s t).1.succ, (gidx s t).2)

theorem bits_gw : ∀ (s : ℕ) (z : Val (gw s)) (t : slots (gw s)),
    bits (gw s) z t = gget s z (gidx s t).1 (gidx s t).2
  | 0, _, t => t.elim
  | s + 1, z, .inl (.inl ()) => rfl
  | s + 1, z, .inl (.inr ()) => rfl
  | s + 1, z, .inr t => by
    simp only [gidx, gget, Fin.cases_succ]
    exact bits_gw s z.2 t

/-- Apply the gates in parallel. -/
def gates : (s : ℕ) → (Fin s → Bool → Bool → Bool) → Val (gw s) → Val (word s)
  | 0, _, _ => ()
  | s + 1, op, z => (op 0 z.1.1 z.1.2, gates s (fun i => op i.succ) z.2)

theorem wget_gates : ∀ (s : ℕ) (op : Fin s → Bool → Bool → Bool) (z : Val (gw s)) (k : Fin s),
    wget s (gates s op z) k = op k (gget s z k false) (gget s z k true)
  | 0, _, _, k => k.elim0
  | s + 1, op, z, k => by
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [wget, gates, gget]
    · simp only [wget, gates, gget, Fin.cases_succ]
      exact wget_gates s _ z.2 j

/-! ## Networks -/

variable (F : Type) [Field F]

theorem DNet.congr {a b : Wire} {f g : Val a → Val b} {m : ℕ} (h : DNet F a b f m)
    (e : ∀ x, f x = g x) : DNet F a b g m := by
  have : f = g := funext e
  subst this
  exact h

/-- `k` copies of a bit. -/
def rep : (k : ℕ) → Bool → Val (word k)
  | 0, _ => ()
  | k + 1, b => (b, rep k b)

theorem bits_rep : ∀ (k : ℕ) (b : Bool) (j : slots (word k)), bits (word k) (rep k b) j = b
  | 0, _, j => j.elim
  | _ + 1, _, .inl () => rfl
  | k + 1, b, .inr j => bits_rep k b j

theorem fanout : ∀ k : ℕ, DNet F .bit (word k) (rep k) (2 * k + 1)
  | 0 => (DNet.discard F .bit).mono (by simp [wd])
  | k + 1 => by
    have h := (DNet.dup F .bit).comp ((DNet.id F .bit).par (fanout k))
    exact (DNet.congr F h (fun x => rfl)).mono (by simp [wd]; omega)

/-- The bundle whose bit at slot `j` is the input bit at slot `σ j`. -/
def select {a b : Wire} (σ : slots b → slots a) (x : Val a) : Val b :=
  (bits b).symm (fun j => bits a x (σ j))

@[simp] theorem bits_select {a b : Wire} (σ : slots b → slots a) (x : Val a) (j : slots b) :
    bits b (select σ x) j = bits a x (σ j) := by
  simp [select]

/-- Left component of a sum known to be on the left. -/
def leftOf {α β : Type} : (s : α ⊕ β) → s.isLeft = true → α
  | .inl a, _ => a
  | .inr _, h => absurd h (by simp)

def rightOf {α β : Type} : (s : α ⊕ β) → ¬ s.isLeft = true → β
  | .inr b, _ => b
  | .inl _, h => absurd rfl h

theorem eq_inl_leftOf {α β : Type} : ∀ (s : α ⊕ β) (h : s.isLeft = true), s = .inl (leftOf s h)
  | .inl _, _ => rfl
  | .inr _, h => absurd h (by simp)

theorem eq_inr_rightOf {α β : Type} :
    ∀ (s : α ⊕ β) (h : ¬ s.isLeft = true), s = .inr (rightOf s h)
  | .inr _, _ => rfl
  | .inl _, h => absurd rfl h

theorem bits_leftOf {a₁ a₂ : Wire} (x : Val (.pair a₁ a₂)) :
    ∀ (s : slots (.pair a₁ a₂)) (h : s.isLeft = true),
      bits a₁ x.1 (leftOf s h) = bits (.pair a₁ a₂) x s
  | .inl _, _ => rfl
  | .inr _, h => absurd h (by simp)

theorem bits_rightOf {a₁ a₂ : Wire} (x : Val (.pair a₁ a₂)) :
    ∀ (s : slots (.pair a₁ a₂)) (h : ¬ s.isLeft = true),
      bits a₂ x.2 (rightOf s h) = bits (.pair a₁ a₂) x s
  | .inr _, _ => rfl
  | .inl _, h => absurd rfl h

/-- Copying and rearranging bits costs at most `wd a + 2 * wd b` vertices. -/
theorem select_net : ∀ (a b : Wire) (σ : slots b → slots a),
    DNet F a b (select σ) (wd a + 2 * wd b)
  | .unit, b, σ => by
    have : IsEmpty (slots b) := ⟨fun j => (σ j).elim⟩
    let e : slots b ≃ slots .unit := Equiv.equivOfIsEmpty _ _
    have h := (DNet.id F .unit).post (rewire_reindex e)
    refine (DNet.congr F h (fun x => ?_)).mono (Nat.zero_le _)
    apply (bits b).injective
    funext j
    exact isEmptyElim j
  | .bit, b, σ => by
    let e : slots b ≃ slots (word (wd b)) := Fintype.equivOfCardEq (by simp)
    have h := (fanout F (wd b)).post (rewire_reindex e)
    refine (DNet.congr F h (fun x => ?_)).mono (by simp [wd])
    apply (bits b).injective
    funext j
    simp only [bits_reindex, bits_rep, bits_select]
    rfl
  | .pair a₁ a₂, b, σ => by
    classical
    let p : slots b → Prop := fun j => (σ j).isLeft = true
    let P := {j // p j}
    let Q := {j // ¬ p j}
    let k₁ := Fintype.card P
    let k₂ := Fintype.card Q
    let e₁ : P ≃ slots (word k₁) := Fintype.equivOfCardEq (by simp [k₁])
    let e₂ : Q ≃ slots (word k₂) := Fintype.equivOfCardEq (by simp [k₂])
    let σ₁ : slots (word k₁) → slots a₁ := fun t => leftOf (σ (e₁.symm t).1) (e₁.symm t).2
    let σ₂ : slots (word k₂) → slots a₂ := fun t => rightOf (σ (e₂.symm t).1) (e₂.symm t).2
    let E : slots b ≃ slots (.pair (word k₁) (word k₂)) :=
      (Equiv.sumCompl p).symm.trans (e₁.sumCongr e₂)
    have hk : k₁ + k₂ = wd b := by
      have := Fintype.card_congr (Equiv.sumCompl p)
      simpa [Fintype.card_sum, k₁, k₂, P, Q] using this
    have h := ((select_net a₁ (word k₁) σ₁).par (select_net a₂ (word k₂) σ₂)).post
      (rewire_reindex E)
    refine (DNet.congr F h (fun x => ?_)).mono (by simp only [wd, wd_word]; omega)
    apply (bits b).injective
    funext j
    rw [bits_reindex, bits_select]
    by_cases hj : p j
    · have hE : E j = .inl (e₁ ⟨j, hj⟩) := by
        show Sum.map _ _ ((Equiv.sumCompl p).symm j) = _
        rw [Equiv.sumCompl_symm_apply_of_pos hj]
        rfl
      rw [hE]
      show bits (word k₁) (select σ₁ x.1) (e₁ ⟨j, hj⟩) = _
      rw [bits_select]
      simp only [σ₁, Equiv.symm_apply_apply]
      exact bits_leftOf x (σ j) hj
    · have hE : E j = .inr (e₂ ⟨j, hj⟩) := by
        show Sum.map _ _ ((Equiv.sumCompl p).symm j) = _
        rw [Equiv.sumCompl_symm_apply_of_neg hj]
        rfl
      rw [hE]
      show bits (word k₂) (select σ₂ x.2) (e₂ ⟨j, hj⟩) = _
      rw [bits_select]
      simp only [σ₂, Equiv.symm_apply_apply]
      exact bits_rightOf x (σ j) hj

theorem gates_net : ∀ (s : ℕ) (op : Fin s → Bool → Bool → Bool),
    DNet F (gw s) (word s) (gates s op) s
  | 0, _ => DNet.congr F (DNet.id F .unit) (fun _ => rfl)
  | s + 1, op => by
    have h := (DNet.table F (.pair .bit .bit) .bit (fun p => op 0 p.1 p.2) (by decide)).par
      (gates_net s (fun i => op i.succ))
    exact (DNet.congr F h (fun _ => rfl)).mono (by omega)

/-! ## From circuits to networks -/

section Translate

variable {F} {n : ℕ} (a : Wire) (ι : Fin n → slots a) (C : Circuit n)

/-- The circuit input read from a bundle. -/
def inp (x : Val a) : Fin n → Bool := fun i => bits a x (ι i)

/-- The slot holding node `j`, given the gate values in a word. -/
def nslot (j : Fin (n + C.size)) : slots (.pair a (word C.size)) :=
  if h : (j : ℕ) < n then .inl (ι ⟨j, h⟩)
  else .inr (wslot C.size ⟨j - n, by have := j.isLt; omega⟩)

theorem bits_nslot (x : Val a) (z : Val (word C.size)) (j : Fin (n + C.size)) :
    bits (.pair a (word C.size)) (x, z) (nslot a ι C j) = C.node (inp a ι x) (wget _ z) j := by
  unfold nslot Circuit.node
  by_cases h : (j : ℕ) < n
  · simp only [h, dite_true]
    rfl
  · simp only [h, dite_false]
    exact bits_wslot _ z _

/-- Where each gate input and the output read from. -/
def wiring : slots (.pair (gw C.size) .bit) → slots (.pair a (word C.size))
  | .inl t => nslot a ι C (C.src (gidx _ t).1 (gidx _ t).2)
  | .inr () => nslot a ι C C.out

/-- One pass of the circuit: read the nodes, apply all gates, and expose the output. -/
def step (y : Val (.pair a (word C.size))) : Val (.pair .bit (word C.size)) :=
  let q := select (wiring a ι C) y
  (q.2, gates C.size C.op q.1)

theorem step_net : DNet F (.pair a (word C.size)) (.pair .bit (word C.size)) (step a ι C)
    (wd a + 6 * C.size + 3) := by
  have h := ((select_net F _ _ (wiring a ι C)).comp
    ((gates_net F C.size C.op).par (DNet.id F .bit))).post (Rewire.swap _ _)
  refine (DNet.congr F h (fun y => rfl)).mono ?_
  simp only [wd, wd_word]
  have : ∀ s, wd (gw s) = 2 * s := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => simp [wd, ih]; ring
  rw [this]
  omega

theorem step_fst (x : Val a) (z : Val (word C.size)) :
    (step a ι C (x, z)).1 = C.node (inp a ι x) (wget _ z) C.out := by
  simp only [step]
  show bits (.pair (gw C.size) .bit) (select (wiring a ι C) (x, z)) (.inr ()) = _
  rw [bits_select]
  exact bits_nslot a ι C x z C.out

theorem wget_step_snd (x : Val a) (z : Val (word C.size)) (k : Fin C.size) :
    wget _ (step a ι C (x, z)).2 k =
      C.op k (C.node (inp a ι x) (wget _ z) (C.src k false))
        (C.node (inp a ι x) (wget _ z) (C.src k true)) := by
  simp only [step]
  rw [wget_gates]
  have hb : ∀ b, gget C.size (select (wiring a ι C) (x, z)).1 k b =
      C.node (inp a ι x) (wget _ z) (C.src k b) := by
    intro b
    -- the slot of gate `k`, input `b`
    have : ∀ (s : ℕ) (q : Val (gw s)) (k : Fin s) (b : Bool),
        ∃ t, gidx s t = (k, b) := by
      intro s
      induction s with
      | zero => intro _ k; exact k.elim0
      | succ s ih =>
        intro q k b
        refine Fin.cases ?_ (fun j => ?_) k
        · cases b
          · exact ⟨.inl (.inl ()), rfl⟩
          · exact ⟨.inl (.inr ()), rfl⟩
        · obtain ⟨t, ht⟩ := ih q.2 j b
          exact ⟨.inr t, by simp [gidx, ht]⟩
    obtain ⟨t, ht⟩ := this C.size (select (wiring a ι C) (x, z)).1 k b
    have h1 := bits_gw C.size (select (wiring a ι C) (x, z)).1 t
    rw [ht] at h1
    rw [← h1]
    show bits (.pair (gw C.size) .bit) (select (wiring a ι C) (x, z)) (.inl t) = _
    rw [bits_select]
    simp only [wiring, ht]
    exact bits_nslot a ι C x z _
  rw [hb, hb]

theorem step_fixed (x : Val a) (y : Bool) (z : Val (word C.size)) :
    step a ι C (x, z) = (y, z) ↔
      z = wenc _ (C.gateVal (inp a ι x)) ∧ y = C.eval (inp a ι x) := by
  constructor
  · intro h
    have h2 : (step a ι C (x, z)).2 = z := congrArg Prod.snd h
    have hc : C.Consistent (inp a ι x) (wget _ z) := by
      intro k
      rw [← wget_step_snd a ι C x z k, h2]
    rw [Circuit.consistent_iff] at hc
    have hz : z = wenc _ (C.gateVal (inp a ι x)) := by
      rw [← hc, wenc_wget]
    refine ⟨hz, ?_⟩
    have h1 : (step a ι C (x, z)).1 = y := congrArg Prod.fst h
    rw [← h1, step_fst, C.node_eq_val (by rw [Circuit.consistent_iff]; exact hc)]
    rfl
  · rintro ⟨rfl, rfl⟩
    apply Prod.ext
    · rw [step_fst, wget_wenc, C.node_eq_val (C.consistent_gateVal _)]
      rfl
    · apply (show Function.Injective (wget C.size) from fun u v huv => by
        rw [← wenc_wget _ u, ← wenc_wget _ v, huv])
      funext k
      rw [wget_step_snd, wget_wenc, C.node_eq_val (C.consistent_gateVal _),
        C.node_eq_val (C.consistent_gateVal _)]
      exact (C.val_gate _ k).symm

/-- **Translation.** A circuit with `s` gates gives a trivalent network with at most
`wd a + 6 s + 4` vertices representing its output, over every field. -/
theorem circuit_net :
    ∃ v ≤ wd a + 6 * C.size + 4,
      Net F a .unit (fun x _ => if C.eval (inp a ι x) then 1 else 0) v := by
  obtain ⟨v, hv, hN⟩ := step_net (F := F) a ι C
  have hT := hN.trace
  have hP := hT.comp (Net.table .bit .unit (fun (b : Bool) (_ : Unit) => if b then (1 : F) else 0)
    (by decide))
  refine ⟨v + 1, by omega, ?_⟩
  convert hP using 1
  funext x u
  have key : ∀ (y : Bool),
      (∑ z : Val (word C.size), if step a ι C (x, z) = (y, z) then (1 : F) else 0) =
        if y = C.eval (inp a ι x) then 1 else 0 := by
    intro y
    have hpt : ∀ z : Val (word C.size),
        (if step a ι C (x, z) = (y, z) then (1 : F) else 0) =
          if (z = wenc _ (C.gateVal (inp a ι x)) ∧ y = C.eval (inp a ι x)) then 1 else 0 := by
      intro z
      by_cases h : step a ι C (x, z) = (y, z)
      · rw [ite_eq_left h, ite_eq_left ((step_fixed a ι C x y z).mp h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ((step_fixed a ι C x y z).mpr h'))]
    rw [Finset.sum_congr rfl (fun z _ => hpt z)]
    by_cases hy : y = C.eval (inp a ι x)
    · simp [hy]
    · simp [hy]
  simp_rw [key]
  rw [Fintype.sum_bool]
  cases C.eval (inp a ι x) <;> simp

end Translate

/-! ## The lower bound -/

/-- `C` decides element distinctness of `2^w` words of `2w` bits, read through an arbitrary
bijection `e` between circuit inputs and the bit positions of the list. -/
def Computes (w : ℕ) {n : ℕ} (e : Fin n ≃ slots (tree w (word (2 * w))))
    (C : Circuit n) : Prop :=
  ∀ y : Fin n → Bool,
    C.eval y = decide (flatten w ((bits (tree w (word (2 * w)))).symm (fun j => y (e.symm j)))).Nodup

theorem realizes_of_circuit {w n : ℕ} (e : Fin n ≃ slots (tree w (word (2 * w))))
    (C : Circuit n) (hC : Computes w e C) :
    ∃ m : ℕ, m ≤ 2 * listBits w + 6 * C.size + 4 ∧ Realizes F w 1 m := by
  let ι : Fin n → slots (lists w 1) := fun i => .inl (e i)
  obtain ⟨v, hv, hN⟩ := circuit_net (F := F) (lists w 1) ι C
  refine ⟨v + 1 * listBits w, ?_, v, ?_, rfl⟩
  · have := wd_lists w 1
    omega
  · convert hN using 1
    funext x u
    have hx : (bits (tree w (word (2 * w)))).symm
        (fun j => inp (lists w 1) ι x (e.symm j)) = x.1 := by
      apply (bits _).injective
      funext j
      simp only [Equiv.apply_symm_apply, inp, ι]
      try rfl
    simp only [distinctPower, mul_one]
    rw [hC (inp (lists w 1) ι x), hx]
    by_cases hd : (flatten w x.1).Nodup <;> simp [hd]

/-- **Main theorem.** Over every finite field the formal Theorem 2.2 gives: every Boolean
circuit over the full binary basis deciding element distinctness of `2^w` words of `2w` bits
has `size` with `N w^σ < 18 size + 6 N + 12`, where `N = 2w 2^w` is the input length. -/
theorem circuit_lower_bound :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop,
      ∀ {n : ℕ} (e : Fin n ≃ slots (tree w (word (2 * w)))) (C : Circuit n),
        Computes w e C →
          (listBits w : ℝ) * (w : ℝ) ^ σ < 18 * C.size + 6 * listBits w + 12 := by
  obtain ⟨σ, hσ, hev⟩ := BatchDescent.manyList (ZMod 2)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with w hw hw1
  intro n e C hC
  obtain ⟨m, hm, hR⟩ := realizes_of_circuit (ZMod 2) e C hC
  have h1 : 1 ≤ listBits w := by
    unfold listBits
    have := Nat.one_le_two_pow (n := w)
    nlinarith
  have := hw 1 m le_rfl h1 hR
  have hm' : (m : ℝ) ≤ 2 * listBits w + 6 * C.size + 4 := by exact_mod_cast hm
  simp only [Nat.cast_one, one_mul] at this
  linarith

/-- **No linear-size circuits.** For every constant `c`, for all large `w`, every circuit for
element distinctness of `2^w` words of `2w` bits has more than `c N` gates. -/
theorem superlinear (c : ℝ) :
    ∀ᶠ w : ℕ in atTop,
      ∀ {n : ℕ} (e : Fin n ≃ slots (tree w (word (2 * w)))) (C : Circuit n),
        Computes w e C → c * listBits w < C.size := by
  obtain ⟨σ, hσ, hev⟩ := circuit_lower_bound
  have ht : Tendsto (fun w : ℕ => (w : ℝ) ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hev, ht.eventually_ge_atTop (18 * (c + 1) + 6), eventually_ge_atTop 1]
    with w hw hpow hw1
  intro n e C hC
  have hb := hw e C hC
  have hN : (1 : ℝ) ≤ listBits w := by
    have : 1 ≤ listBits w := by
      unfold listBits
      have := Nat.one_le_two_pow (n := w)
      nlinarith
    exact_mod_cast this
  have hmul : (listBits w : ℝ) * (18 * (c + 1) + 6) ≤ (listBits w : ℝ) * (w : ℝ) ^ σ :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  nlinarith

/-! ## Restatement with CSLib circuits and Complexitylib's element distinctness

The statements below use only definitions from CSLib (`Cslib.Circuits.Circuit`, its evaluation,
`Circuit.Computes`, `single`, `complexity`, the full binary basis and the De Morgan basis) and
from Complexitylib (`Cslib.Circuits.Boolean.elementDistinctness`). -/

section Bridge

open Cslib.Circuits (Wire Line Program Signature Interpretation single fullSignature
  fullInterpretation complexity)
open Cslib.Circuits.Boolean (elementDistinctness)

universe v

variable {S : Signature.{v}} {n : ℕ}

/-- The node index of a CSLib wire. -/
def wireIdx {g : ℕ} : Wire n g → Fin (n + g)
  | .input i => Fin.castAdd g i
  | .gate j => Fin.natAdd n j

/-- Node values on natural-number indices. -/
def tr (x : Fin n → Bool) {G : ℕ} (g : Fin G → Bool) (j : ℕ) : Bool :=
  if h : j < n then x ⟨j, h⟩ else if h' : j - n < G then g ⟨j - n, h'⟩ else false

theorem tr_wireIdx (x : Fin n → Bool) {g : ℕ} (pr : Fin g → Bool) (w : Wire n g) :
    tr x pr (wireIdx w) = Cslib.Circuits.Wire.elim x pr w := by
  cases w with
  | input i =>
    unfold tr wireIdx
    have h : ((Fin.castAdd g i : Fin (n + g)) : ℕ) < n := by simp
    rw [dite_eq_left h]
    rfl
  | gate j =>
    unfold tr wireIdx
    have h1 : ¬ ((Fin.natAdd n j : Fin (n + g)) : ℕ) < n := by simp
    have h2 : ((Fin.natAdd n j : Fin (n + g)) : ℕ) - n < g := by simp
    rw [dite_eq_right h1, dite_eq_left h2, Cslib.Circuits.Wire.elim_gate]
    congr 1
    ext
    simp

theorem tr_extend (x : Fin n → Bool) {g : ℕ} (full : Fin (g + 1) → Bool) (prior : Fin g → Bool)
    (h : ∀ j : Fin g, full j.castSucc = prior j) (i : ℕ) (hi : i < n + g) :
    tr x full i = tr x prior i := by
  unfold tr
  by_cases h1 : i < n
  · rw [dite_eq_left h1, dite_eq_left h1]
  · have h2 : i - n < g := by omega
    have h3 : i - n < g + 1 := by omega
    rw [dite_eq_right h1, dite_eq_right h1, dite_eq_left h3, dite_eq_left h2]
    exact h ⟨i - n, h2⟩

theorem node_eq_tr (C : Circuit n) (x : Fin n → Bool) (g : Fin C.size → Bool)
    (j : Fin (n + C.size)) : C.node x g j = tr x g j := by
  unfold Circuit.node tr
  by_cases h : (j : ℕ) < n
  · rw [dite_eq_left h, dite_eq_left h]
  · have h' : (j : ℕ) - n < C.size := by have := j.isLt; omega
    rw [dite_eq_right h, dite_eq_right h, dite_eq_left h']

/-- A gate of arity at most two as a binary Boolean function. -/
def lineOp (I : Interpretation S Bool) (op : S.Op) : Bool → Bool → Bool :=
  fun a b => I op (fun i => if (i : ℕ) = 0 then a else b)

/-- The two sources of a gate of arity at most two (repeated or arbitrary when unused). -/
def lineSrc (hn : 0 < n) {g : ℕ} (line : Line S n g) (b : Bool) : Fin (n + g) :=
  if h1 : 0 < S.Arity line.op then
    if h2 : b = true ∧ 1 < S.Arity line.op then wireIdx (line.wires ⟨1, h2.2⟩)
    else wireIdx (line.wires ⟨0, h1⟩)
  else ⟨0, by omega⟩

theorem lineOp_spec (I : Interpretation S Bool) (hn : 0 < n) {g : ℕ} (line : Line S n g)
    (h : S.Arity line.op ≤ 2) (v : Wire n g → Bool) (val : ℕ → Bool)
    (hv : ∀ w, val (wireIdx w) = v w) :
    lineOp I line.op (val (lineSrc hn line false)) (val (lineSrc hn line true)) =
      I line.op (v ∘ line.wires) := by
  unfold lineOp
  congr 1
  funext i
  have hi := i.isLt
  by_cases h0 : (i : ℕ) = 0
  · rw [ite_eq_left h0]
    have h1 : 0 < S.Arity line.op := by omega
    have hi0 : i = ⟨0, h1⟩ := Fin.ext h0
    subst hi0
    simp [lineSrc, h1, hv]
  · rw [ite_eq_right h0]
    have h2 : 1 < S.Arity line.op := by omega
    have h1 : 0 < S.Arity line.op := by omega
    have hi1 : i = ⟨1, h2⟩ := Fin.ext (by show (i : ℕ) = 1; omega)
    subst hi1
    simp [lineSrc, h1, h2, hv]

/-- The gate functions of a CSLib program. -/
def convOp (I : Interpretation S Bool) : {g : ℕ} → Program S n g → Fin g → Bool → Bool → Bool
  | _, .empty, k => k.elim0
  | _, .gate p line, k => Fin.lastCases (lineOp I line.op) (convOp I p) k

/-- The gate sources of a CSLib program. -/
def convSrc (hn : 0 < n) : {g : ℕ} → (p : Program S n g) → (k : Fin g) → Bool → Fin (n + k)
  | _, .empty, k => k.elim0
  | _, .gate p line, k =>
    Fin.lastCases (motive := fun k => Bool → Fin (n + (k : ℕ)))
      (fun b => lineSrc hn line b) (fun j b => convSrc hn p j b) k

/-- A CSLib program with a designated output, as a circuit of the same size. -/
@[reducible] def ofProgram (I : Interpretation S Bool) (hn : 0 < n) {g : ℕ} (p : Program S n g)
    (out : Fin (n + g)) : Circuit n where
  size := g
  op := convOp I p
  src₁ k := convSrc hn p k false
  src₂ k := convSrc hn p k true
  out := out

theorem eval_spec (I : Interpretation S Bool) (hn : 0 < n) (x : Fin n → Bool) :
    ∀ {g : ℕ} (p : Program S n g), p.FanInAtMost 2 → ∀ k : Fin g,
      p.eval I x k = convOp I p k (tr x (p.eval I x) (convSrc hn p k false))
        (tr x (p.eval I x) (convSrc hn p k true))
  | _, .empty, _, k => k.elim0
  | _, .gate p line, hp, k => by
    have hp2 : p.FanInAtMost 2 ∧ S.Arity line.op ≤ 2 := hp
    have hfull : ∀ j, (Program.gate p line).eval I x j.castSucc = p.eval I x j :=
      fun j => Cslib.Circuits.Program.eval_gate_castSucc p line I x j
    refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [Cslib.Circuits.Program.eval_gate_last]
      simp only [convOp, convSrc, Fin.lastCases_last]
      rw [tr_extend x _ _ hfull _ (lineSrc hn line false).isLt,
        tr_extend x _ _ hfull _ (lineSrc hn line true).isLt,
        lineOp_spec I hn line hp2.2 (Cslib.Circuits.Wire.elim x (p.eval I x))
          (tr x (p.eval I x)) (tr_wireIdx x _)]
      rfl
    · rw [hfull j]
      simp only [convOp, convSrc, Fin.lastCases_castSucc]
      have hj := j.isLt
      rw [tr_extend x _ _ hfull _ (by have := (convSrc hn p j false).isLt; omega),
        tr_extend x _ _ hfull _ (by have := (convSrc hn p j true).isLt; omega)]
      exact eval_spec I hn x p hp2.1 j

theorem consistent_ofProgram (I : Interpretation S Bool) (hn : 0 < n) {g : ℕ}
    (p : Program S n g) (hp : p.FanInAtMost 2) (out : Fin (n + g)) (x : Fin n → Bool) :
    (ofProgram I hn p out).Consistent x (p.eval I x) := by
  intro k
  have hs : ∀ b, ((ofProgram I hn p out).src k b : ℕ) = (convSrc hn p k b : ℕ) := by
    intro b
    cases b <;> rfl
  have e1 := node_eq_tr (ofProgram I hn p out) x (p.eval I x) ((ofProgram I hn p out).src k false)
  have e2 := node_eq_tr (ofProgram I hn p out) x (p.eval I x) ((ofProgram I hn p out).src k true)
  rw [hs] at e1 e2
  rw [e1, e2]
  exact eval_spec I hn x p hp k

/-- A CSLib program of fan-in at most two and the converted circuit compute the same value
on every wire. -/
theorem ofProgram_eval_wire (I : Interpretation S Bool) (hn : 0 < n) {g : ℕ}
    (p : Program S n g) (hp : p.FanInAtMost 2) (o : Wire n g) (x : Fin n → Bool) :
    (ofProgram I hn p (wireIdx o)).eval x = Cslib.Circuits.Wire.elim x (p.eval I x) o := by
  have hc := consistent_ofProgram I hn p hp (wireIdx o) x
  calc (ofProgram I hn p (wireIdx o)).eval x
      = (ofProgram I hn p (wireIdx o)).val x (wireIdx o) := rfl
    _ = (ofProgram I hn p (wireIdx o)).node x (p.eval I x) (wireIdx o) :=
        ((ofProgram I hn p (wireIdx o)).node_eq_val hc (wireIdx o)).symm
    _ = tr x (p.eval I x) (wireIdx o) := node_eq_tr _ _ _ _
    _ = Cslib.Circuits.Wire.elim x (p.eval I x) o := tr_wireIdx x _ o

/-- A CSLib circuit of fan-in at most two and the converted circuit compute the same output. -/
theorem ofProgram_eval (I : Interpretation S Bool) (hn : 0 < n)
    (C : Cslib.Circuits.Circuit S n 1) (hC : C.FanInAtMost 2) (x : Fin n → Bool) :
    (ofProgram I hn C.program (wireIdx (C.outputs 0))).eval x = C.eval I x 0 :=
  ofProgram_eval_wire I hn C.program hC (C.outputs 0) x

/-! ### Matching the input layouts -/

/-- Leaf `i` of a tree, in the order of `flatten`. -/
def tleaf {a : Wire} : (w : ℕ) → Val (tree w a) → Fin (2 ^ w) → Val a
  | 0, x, _ => x
  | w + 1, x, i =>
    if h : (i : ℕ) < 2 ^ w then tleaf w x.1 ⟨i, h⟩
    else tleaf w x.2 ⟨i - 2 ^ w, by have h1 := i.isLt; have h2 : 2 ^ (w + 1) = 2 ^ w * 2 := Nat.pow_succ 2 w; omega⟩

theorem length_flatten {a : Wire} : ∀ (w : ℕ) (x : Val (tree w a)), (flatten w x).length = 2 ^ w
  | 0, _ => rfl
  | w + 1, x => by
    simp only [flatten, List.length_append, length_flatten w, pow_succ]
    ring

theorem flatten_eq_ofFn {a : Wire} : ∀ (w : ℕ) (x : Val (tree w a)),
    flatten w x = List.ofFn (tleaf w x)
  | 0, x => rfl
  | w + 1, x => by
    have h1 := flatten_eq_ofFn w x.1
    have h2 := flatten_eq_ofFn w x.2
    simp only [flatten, h1, h2]
    apply List.ext_getElem
    · simp only [List.length_append, List.length_ofFn, pow_succ]
      ring
    · intro i hi1 hi2
      simp only [List.getElem_append, List.getElem_ofFn, List.length_ofFn, tleaf]

/-- The slot of a tree holding slot `s` of leaf `i`. -/
def tslot {a : Wire} : (w : ℕ) → Fin (2 ^ w) → slots a → slots (tree w a)
  | 0, _, s => s
  | w + 1, i, s =>
    if h : (i : ℕ) < 2 ^ w then .inl (tslot w ⟨i, h⟩ s)
    else .inr (tslot w ⟨i - 2 ^ w, by have h1 := i.isLt; have h2 : 2 ^ (w + 1) = 2 ^ w * 2 := Nat.pow_succ 2 w; omega⟩ s)

theorem bits_tslot {a : Wire} : ∀ (w : ℕ) (x : Val (tree w a)) (i : Fin (2 ^ w)) (s : slots a),
    bits (tree w a) x (tslot w i s) = bits a (tleaf w x i) s
  | 0, _, _, _ => rfl
  | w + 1, x, i, s => by
    by_cases h : (i : ℕ) < 2 ^ w
    · simp only [tslot, tleaf, h, dite_true]
      exact bits_tslot w x.1 _ s
    · simp only [tslot, tleaf, h, dite_false]
      exact bits_tslot w x.2 _ s

theorem tslot_inj {a : Wire} : ∀ (w : ℕ) (i j : Fin (2 ^ w)) (s t : slots a),
    tslot w i s = tslot w j t → i = j ∧ s = t
  | 0, i, j, s, t, h => ⟨Fin.ext (by have hi := i.isLt; have hj := j.isLt; simp only [pow_zero] at hi hj; omega), h⟩
  | w + 1, i, j, s, t, h => by
    by_cases hi : (i : ℕ) < 2 ^ w <;> by_cases hj : (j : ℕ) < 2 ^ w <;>
      simp only [tslot, hi, hj, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at h
    · obtain ⟨h1, h2⟩ := tslot_inj w _ _ s t h
      exact ⟨Fin.ext (by simpa using congrArg Fin.val h1), h2⟩
    · obtain ⟨h1, h2⟩ := tslot_inj w _ _ s t h
      refine ⟨Fin.ext ?_, h2⟩
      have := congrArg Fin.val h1
      simp only at this
      omega

/-- Leaves and their slots enumerate the slots of a tree. -/
noncomputable def tEquiv (a : Wire) (w : ℕ) : Fin (2 ^ w) × slots a ≃ slots (tree w a) :=
  Equiv.ofBijective (fun p => tslot w p.1 p.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun p q h => Prod.ext_iff.mpr (tslot_inj w _ _ _ _ h), by simp [wd_tree]⟩)

theorem wslot_inj : ∀ (s : ℕ), Function.Injective (wslot s)
  | 0 => fun i => i.elim0
  | s + 1 => by
    intro i j h
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j' => simp [wslot] at h
    | succ i' =>
      induction j using Fin.cases with
      | zero => simp [wslot] at h
      | succ j' =>
        simp only [wslot, Fin.cases_succ, Sum.inr.injEq] at h
        exact congrArg Fin.succ (wslot_inj s h)

/-- Entries of a word enumerate its slots. -/
noncomputable def wEquiv (s : ℕ) : Fin s ≃ slots (word s) :=
  Equiv.ofBijective (wslot s)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨wslot_inj s, by simp⟩)

/-- Complexitylib's block layout: bit `b` of block `i` is input `finProdFinEquiv (i, b)`. -/
noncomputable def layout (w : ℕ) : Fin (2 ^ w * (2 * w)) ≃ slots (tree w (word (2 * w))) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (wEquiv (2 * w))).trans (tEquiv _ w))

theorem layout_apply (w : ℕ) (i : Fin (2 ^ w)) (b : Fin (2 * w)) :
    layout w (finProdFinEquiv (i, b)) = tslot w i (wslot (2 * w) b) := by
  simp [layout, tEquiv, wEquiv]

theorem computes_of_ed {w : ℕ} (C : Circuit (2 ^ w * (2 * w)))
    (h : ∀ y, C.eval y = elementDistinctness (2 ^ w) (2 * w) y) : Computes w (layout w) C := by
  intro y
  rw [h y]
  set X := (bits (tree w (word (2 * w)))).symm (fun j => y ((layout w).symm j)) with hX
  have hblock : Cslib.BitString.block y = fun i => wget (2 * w) (tleaf w X i) := by
    funext i b
    rw [← bits_wslot, ← bits_tslot, hX, Equiv.apply_symm_apply, ← layout_apply,
      Equiv.symm_apply_apply]
    rfl
  have hwget : Function.Injective (wget (2 * w)) := fun u v huv => by
    rw [← wenc_wget _ u, ← wenc_wget _ v, huv]
  unfold elementDistinctness
  rw [hblock, flatten_eq_ofFn]
  exact decide_eq_decide.mpr ((hwget.of_comp_iff (tleaf w X)).trans List.nodup_ofFn.symm)

/-! ### The lower bound in CSLib's terms -/

/-- **Lower bound, CSLib form.** Over any basis of fan-in at most two, every circuit computing
Complexitylib's `elementDistinctness (2^w) (2w)` on `N = 2^w · 2w` inputs has
`N w^σ < 18 size + 6 N + 12`. -/
theorem cslib_lower_bound :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop,
      ∀ {S : Signature.{v}} (I : Interpretation S Bool)
        (C : Cslib.Circuits.Circuit S (2 ^ w * (2 * w)) 1),
        C.FanInAtMost 2 → C.Computes I (single (elementDistinctness (2 ^ w) (2 * w))) →
          ((2 ^ w * (2 * w) : ℕ) : ℝ) * (w : ℝ) ^ σ <
            18 * C.size + 6 * ((2 ^ w * (2 * w) : ℕ) : ℝ) + 12 := by
  obtain ⟨σ, hσ, hev⟩ := circuit_lower_bound
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with w hw hw1
  intro S I C hfan hcomp
  have hn : 0 < 2 ^ w * (2 * w) := by positivity
  have hC' : Computes w (layout w) (ofProgram I hn C.program (wireIdx (C.outputs 0))) :=
    computes_of_ed _ (fun y => by
      rw [ofProgram_eval I hn C hfan y]
      exact congrFun (hcomp y) 0)
  have hb := hw (layout w) _ hC'
  have hl : (listBits w : ℝ) = ((2 ^ w * (2 * w) : ℕ) : ℝ) := by
    unfold listBits
    push_cast
    ring
  rw [hl] at hb
  exact hb

/-- **No linear-size circuits, CSLib form.** For every constant `c`, for all large `w`, every
circuit over any basis of fan-in at most two computing `elementDistinctness (2^w) (2w)` has more
than `c N` gates, `N = 2^w · 2w`. -/
theorem cslib_superlinear (c : ℝ) :
    ∀ᶠ w : ℕ in atTop,
      ∀ {S : Signature.{v}} (I : Interpretation S Bool)
        (C : Cslib.Circuits.Circuit S (2 ^ w * (2 * w)) 1),
        C.FanInAtMost 2 → C.Computes I (single (elementDistinctness (2 ^ w) (2 * w))) →
          c * ((2 ^ w * (2 * w) : ℕ) : ℝ) < C.size := by
  obtain ⟨σ, hσ, hev⟩ := cslib_lower_bound.{v}
  have ht : Tendsto (fun w : ℕ => (w : ℝ) ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hev, ht.eventually_ge_atTop (18 * (c + 1) + 6), eventually_ge_atTop 1]
    with w hw hpow hw1
  intro S I C hfan hcomp
  have hb := hw I C hfan hcomp
  have hN : (1 : ℝ) ≤ ((2 ^ w * (2 * w) : ℕ) : ℝ) := by
    have : 1 ≤ 2 ^ w * (2 * w) := by
      have := Nat.one_le_two_pow (n := w)
      nlinarith
    exact_mod_cast this
  have hmul : ((2 ^ w * (2 * w) : ℕ) : ℝ) * (18 * (c + 1) + 6) ≤
      ((2 ^ w * (2 * w) : ℕ) : ℝ) * (w : ℝ) ^ σ :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  nlinarith

theorem fanIn_full : ∀ {g : ℕ} (p : Program (fullSignature 2 Bool) n g), p.FanInAtMost 2
  | _, .empty => trivial
  | _, .gate p line => by
    show p.FanInAtMost 2 ∧ (fullSignature 2 Bool).Arity line.op ≤ 2
    refine ⟨fanIn_full p, ?_⟩
    generalize line.op = op
    cases op <;> simp [fullSignature]

/-- **Circuit complexity over the full binary basis.** For every `c`, for all large `w`, the
natural-number circuit complexity `C(f)` of element distinctness over the full binary basis `B₂`
(CSLib's `complexity`, which requires basis completeness and is therefore non-vacuous) exceeds
`c N`. -/
theorem full_basis_complexity (c : ℕ) :
    ∀ᶠ w : ℕ in atTop,
      c * (2 ^ w * (2 * w)) <
        complexity (fullInterpretation : Interpretation (fullSignature 2 Bool) Bool)
          (single (elementDistinctness (2 ^ w) (2 * w))) := by
  filter_upwards [cslib_superlinear.{0} (c : ℝ)] with w hw
  obtain ⟨C, hC, hsize⟩ :=
    Cslib.Circuits.exists_computesOn_size_eq_complexityOn
      (I := (fullInterpretation : Interpretation (fullSignature 2 Bool) Bool))
      (S := Set.univ) (f := single (elementDistinctness (2 ^ w) (2 * w)))
  change C.size = complexity _ _ at hsize
  rw [← hsize]
  have h := hw _ C (fanIn_full C.program) (fun x => hC (Set.mem_univ x))
  have : ((c * (2 ^ w * (2 * w)) : ℕ) : ℝ) < C.size := by push_cast at h ⊢; linarith
  exact_mod_cast this

/-- **De Morgan circuits.** The same bound for CSLib's De Morgan basis (AND, OR, NOT,
constants). -/
theorem deMorgan_superlinear (c : ℝ) :
    ∀ᶠ w : ℕ in atTop,
      ∀ C : Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature (2 ^ w * (2 * w)) 1,
        C.Computes Cslib.Circuits.Boolean.interpretation
            (single (elementDistinctness (2 ^ w) (2 * w))) →
          c * ((2 ^ w * (2 * w) : ℕ) : ℝ) < C.size := by
  filter_upwards [cslib_superlinear.{0} c] with w hw
  exact fun C hC => hw _ C C.fanInAtMost_two hC

/-- **Circuit complexity over the De Morgan basis.** Natural-number `complexity` form over
CSLib's complete De Morgan basis. -/
theorem deMorgan_complexity (c : ℕ) :
    ∀ᶠ w : ℕ in atTop,
      c * (2 ^ w * (2 * w)) <
        complexity Cslib.Circuits.Boolean.interpretation
          (single (elementDistinctness (2 ^ w) (2 * w))) := by
  filter_upwards [deMorgan_superlinear (c : ℝ)] with w hw
  obtain ⟨C, hC, hsize⟩ :=
    Cslib.Circuits.exists_computesOn_size_eq_complexityOn
      (I := Cslib.Circuits.Boolean.interpretation)
      (S := Set.univ) (f := single (elementDistinctness (2 ^ w) (2 * w)))
  change C.size = complexity _ _ at hsize
  rw [← hsize]
  have h := hw C (fun x => hC (Set.mem_univ x))
  have : ((c * (2 ^ w * (2 * w)) : ℕ) : ℝ) < C.size := by push_cast at h ⊢; linarith
  exact_mod_cast this

end Bridge

end CircuitLowerBound

#print axioms CircuitLowerBound.circuit_lower_bound
#print axioms CircuitLowerBound.superlinear
#print axioms CircuitLowerBound.cslib_lower_bound
#print axioms CircuitLowerBound.cslib_superlinear
#print axioms CircuitLowerBound.full_basis_complexity
#print axioms CircuitLowerBound.deMorgan_superlinear
#print axioms CircuitLowerBound.deMorgan_complexity
