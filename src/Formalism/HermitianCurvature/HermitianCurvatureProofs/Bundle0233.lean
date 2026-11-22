import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0218
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordCorrespondence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightCapelliAsGenerators
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem crag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.RZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpR (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpR, capGen, zgB, Q.RZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem right_capelli_as_generators : CapRAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capR, Q.qmF, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [crag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightGeneratorWordEvaluation
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace FExpR

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rep (m : ℕ∞) (O : Set (B.Mat k r)) (φ : B.Mat k r → E) : Prop :=
  ∃ F : B.Mat k r → E, ContDiffOn ℝ (m : WithTop ℕ∞) F O ∧ ∀ x ∈ O, x ∈ B.GV k r → φ x = F x

theorem rep_mono {m m' : ℕ∞} (hmm : m ≤ m') {O : Set (B.Mat k r)} {φ : B.Mat k r → E} (h : Rep m' O φ) :
    Rep m O φ := by
  obtain ⟨F, hF, he⟩ := h
  exact ⟨F, hF.of_le (by exact_mod_cast hmm), he⟩

theorem rep_RdV {m : ℕ∞} {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {X : B.Mat k r}
    (hX : B.inLie k r X) (h : Rep (m + 1) O φ) : Rep m O (RdV X φ) := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => fderiv ℝ F x (x * X), ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hO (by push_cast; exact le_rfl)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ F x :=
      (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
    exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).deriv

theorem rep_Rw {O : Set (B.Mat k r)} (hO : IsOpen O) {f : B.Mat k r → E} {N : ℕ} (h : Rep (N : ℕ∞) O f)
    (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) :
    Rep (m : ℕ∞) O (B.Rw w f) := by
  induction w generalizing m with
  | nil => exact rep_mono (by exact_mod_cast (by simpa using hle)) h
  | cons X w ih =>
    have e : B.Rw (X :: w) f = RdV X (B.Rw w f) := rfl
    rw [e]
    apply rep_RdV hO (hw X (by simp))
    have := ih (fun Y hY => hw Y (by simp [hY])) (m + 1) (by simp at hle; omega)
    exact_mod_cast this

theorem rep_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {x X : B.Mat k r}
    (hx : x ∈ O) (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (h : Rep ((1 : ℕ) : ℕ∞) O φ) :
    HasDerivAt (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) (RdV X φ x) 0 := by
  obtain ⟨F, hF, he⟩ := h
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
  exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).differentiableAt.hasDerivAt

theorem rdV_congr {O : Set (B.Mat k r)} (hO : IsOpen O) {φ ψ : B.Mat k r → E}
    (he : ∀ y ∈ O, y ∈ B.GV k r → φ y = ψ y) {x X : B.Mat k r} (hx : x ∈ O) (hxG : x ∈ B.GV k r)
    (hX : B.inLie k r X) : RdV X φ x = RdV X ψ x := by
  show deriv (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => ψ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hγ := hasDerivAt_mul_exp_smul_zero x X
  have hγ0 := Formalism.FourierDecayAlt.P.B5.curve_zero x X
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, x * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hx)
  filter_upwards [hmem] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

theorem wsEvalR_append (a b : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E)
    (x : B.Mat k r) : wsEvalR (a ++ b) u f x = wsEvalR a u f x + wsEvalR b u f x := by
  simp [wsEvalR, List.map_append, List.sum_append]

theorem wsEvalR_flatMap {α : Type} (F : α → List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ L : List α, wsEvalR (L.flatMap F) u f x = (L.map fun a => wsEvalR (F a) u f x).sum
  | [] => by simp [wsEvalR]
  | a :: L => by
    rw [List.flatMap_cons, wsEvalR_append, wsEvalR_flatMap F u f x L, List.map_cons, List.sum_cons]

theorem wsEvalR_map_mul (p : Polynomial ℂ) (φ : List (B.Mat k r) → List (B.Mat k r)) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)),
      wsEvalR (ws.map fun t => (p * t.1, φ t.2)) u f x = p.eval u • wsEvalR (ws.map fun t => (t.1, φ t.2)) u f x
  | [] => by simp [wsEvalR]
  | t :: ws => by
    have ih := wsEvalR_map_mul p φ u f x ws
    simp only [wsEvalR, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, Polynomial.eval_mul, mul_smul]

theorem fexp_words : ∀ (gens : List (GenW k r)), (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) →
    ∀ t ∈ fexp gens, t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, B.inLie k r X
  | [], _, t, ht => by
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | gn :: gs, hL, t, ht => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have ih := fexp_words gs hL'
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨dX, hdX, s, hs, rfl⟩
    · have := (ih s hs).1
      refine ⟨?_, (ih s hs).2⟩
      show s.2.length ≤ (gn :: gs).length
      simp only [List.length_cons]; omega
    · have := (ih s hs).1
      refine ⟨?_, ?_⟩
      · show (dX.2 :: s.2).length ≤ (gn :: gs).length
        simp only [List.length_cons]; omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact hL gn (by simp) dX hdX
        · exact (ih s hs).2 X hX

theorem ws_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {x X : B.Mat k r} (hx : x ∈ O)
    (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (u : ℂ) (f : B.Mat k r → E) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)), (∀ t ∈ ws, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f)) →
      HasDerivAt (fun s : ℝ => wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)))
        (wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x) 0
  | [], _ => by
    have e : ∀ y, wsEvalR ([] : List (Polynomial ℂ × List (B.Mat k r))) u f y = (0 : E) := fun y => by
      simp [wsEvalR]
    simp only [List.map_nil, e]
    exact hasDerivAt_const _ _
  | t :: ws, h => by
    have h1 := (rep_hasDerivAt hO hx hxG hX (h t (by simp))).const_smul (t.1.eval u)
    have h2 := ws_hasDerivAt hO hx hxG hX u f ws (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have e1 : (fun s : ℝ => wsEvalR (t :: ws) u f (x * NormedSpace.exp ((s : ℂ) • X))) =
        fun s : ℝ => t.1.eval u • B.Rw t.2 f (x * NormedSpace.exp ((s : ℂ) • X)) +
          wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)) := by
      funext s; simp only [wsEvalR, List.map_cons, List.sum_cons]
    have e2 : wsEvalR ((t :: ws).map fun t => (t.1, X :: t.2)) u f x =
        t.1.eval u • RdV X (B.Rw t.2 f) x + wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x := by
      simp only [wsEvalR, List.map_cons, List.sum_cons] <;> rfl
    rw [e1, e2]
    exact h1.add h2

theorem right_generator_word_evaluation (u : ℂ) : ∀ (gens : List (GenW k r)) (O : Set (B.Mat k r)) (f : B.Mat k r → E), IsOpen O →
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → Rep (gens.length : ℕ∞) O f → ∀ x ∈ O, x ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f x = wsEvalR (fexp gens) u f x
  | [], O, f, _, _, _, x, _, _ => by simp [fexp, wsEvalR, B.Rw]
  | gn :: gs, O, f, hO, hL, hf, x, hx, hxG => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have hf' : Rep (gs.length : ℕ∞) O f := rep_mono (by exact_mod_cast (by simp : gs.length ≤ (gn :: gs).length)) hf
    have IH := right_generator_word_evaluation u gs O f hO hL' hf'
    have hW := fexp_words gs hL'
    have hrep : ∀ t ∈ fexp gs, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f) := fun t ht =>
      rep_Rw hO hf t.2 (hW t ht).2 1 (by have := (hW t ht).1; simp only [List.length_cons]; omega)
    have hD : ∀ X, B.inLie k r X → RdV X (wsEvalR (fexp gs) u f) x =
        wsEvalR ((fexp gs).map fun t => (t.1, X :: t.2)) u f x := fun X hX =>
      (ws_hasDerivAt hO hx hxG hX u f (fexp gs) hrep).deriv
    have hR : wsEvalR (fexp (gn :: gs)) u f x = gn.1.eval u • wsEvalR (fexp gs) u f x +
        (gn.2.map fun dX => dX.1 • wsEvalR ((fexp gs).map fun t => (t.1, dX.2 :: t.2)) u f x).sum := by
      simp only [fexp]
      rw [wsEvalR_append, wsEvalR_flatMap]
      congr 1
      · have := wsEvalR_map_mul gn.1 id u f x (fexp gs)
        simpa using this
      · congr 1
        apply List.map_congr_left
        intro dX _
        have := wsEvalR_map_mul (Polynomial.C dX.1) (fun w => dX.2 :: w) u f x (fexp gs)
        simpa using this
    set Φ := (gs.map fun gn => genOpR gn u).foldr (fun T h => T h) f with hΦdef
    have hΦ : ∀ X, B.inLie k r X → RdV X Φ x = RdV X (wsEvalR (fexp gs) u f) x := fun X hX =>
      rdV_congr hO (fun y hy hyG => IH y hy hyG) hx hxG hX
    rw [hR]
    change gn.1.eval u • Φ x + (gn.2.map fun dX => dX.1 • RdV dX.2 Φ x).sum = _
    rw [IH x hx hxG]
    congr 2
    apply List.map_congr_left
    intro dX hdX
    have hX := hL gn (by simp) dX hdX
    rw [hΦ dX.2 hX, hD dX.2 hX]

end FExpR

theorem right_exponential_evaluation : FExpEvalR := by
  intro k r E _ _ gens u UU f hL hf g hg hgG
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hf g hg
  exact FExpR.right_generator_word_evaluation u gens U f hU hL ⟨f', hf', he⟩ g hgU hgG

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RootVectorActionCutoff
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

def cI (p : Fin (2 * r + k + 1)) : Fin (mdim k r 0) := ⟨p.val, by have := p.isLt; simp [mdim]; omega⟩

theorem posL_cI (p : Fin (2 * r + k + 1)) : posL k r 0 (cI p) = p := Fin.ext (by simp [posL, cI])

theorem cI_inj : Function.Injective (cI (k := k) (r := r)) := fun p q h => Fin.ext (by
  have := congrArg Fin.val h; simpa [cI] using this)

variable (E) in

abbrev SA (hD : IsOpen D) : Subalgebra ℂ (Module.End ℂ (VS k r 0 D E)) :=
  Algebra.adjoin ℂ (Set.range fun p : Fin (mdim k r 0) × Fin (mdim k r 0) => Eh (E := E) (i := 0) hD p.1 p.2)

def EA (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : SA E hD :=
  ⟨Eh hD (cI p) (cI q), Algebra.subset_adjoin ⟨(cI p, cI q), rfl⟩⟩

theorem EA_val (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : (EA (E := E) hD p q : Module.End ℂ (VS k r 0 D E)) =
    Eh hD (cI p) (cI q) := rfl

theorem EA_gl (hD : IsOpen D) : GlRel (EA (E := E) hD) := by
  intro a b c d
  apply Subtype.ext
  have h := Eh_gl (E := E) (i := 0) hD (cI a) (cI b) (cI c) (cI d)
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, EA_val]
  rw [h]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos (congrArg cI hbc), if_pos hbc]; rfl
    · rw [if_neg (fun e => hbc (cI_inj e)), if_neg hbc]; rfl
  · by_cases hda : d = a
    · rw [if_pos (congrArg cI hda), if_pos hda]; rfl
    · rw [if_neg (fun e => hda (cI_inj e)), if_neg hda]; rfl

def La (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) : SA E hD →ₗ[ℂ] E where
  toFun x := ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g
  map_add' x y := by simp
  map_smul' c x := by simp

theorem La_apply (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) (x : SA E hD) :
    La hD v g x = ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g := rfl

theorem leftEq_SA (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (x : SA E hD) :
    ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) := by
  obtain ⟨x, hx⟩ := x
  show ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) → LeftEq k r z 0 D (x v : Mx k r → E)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    intro v hv g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩
    rw [ev_E hD p.1 p.2 v hng, ev_E hD p.1 p.2 v hg]
    exact ((generator_action_preserved E k r z 0 D p.1 p.2 (v : Mx k r → E) (v : Mx k r → E) 1 hD v.2.1 v.2.1).2.1 hN hv) g hg n hn
  | algebraMap c =>
    intro v hv g hg n hn
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg n hn, smul_comm]
  | add y₁ y₂ _ _ h₁ h₂ =>
    intro v hv g hg n hn
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h₁ v hv g hg n hn, h₂ v hv g hg n hn, smul_add]
  | mul y₁ y₂ _ _ h₁ h₂ =>
    intro v hv
    exact h₁ _ (h₂ v hv)

abbrev Tor (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, j ≤ l.val ∧ x = EA hD (eI k r l) (eI k r l)}

theorem comm_Tor (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, j ≤ l.val → p ≠ eI k r l) (hq : ∀ l : Fin r, j ≤ l.val → q ≠ eI k r l) (P : SA E hD)
    (hP : P ∈ Tor hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (eI k r l) (eI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem Tor_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : Tor (E := E) hD j' ≤ Tor hD j :=
  Algebra.adjoin_mono fun _ ⟨l, hl, e⟩ => ⟨l, h.trans hl, e⟩

theorem EA_mem_Tor (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : j ≤ l.val) :
    EA (E := E) hD (eI k r l) (eI k r l) ∈ Tor hD j :=
  Algebra.subset_adjoin ⟨l, h, rfl⟩

end alg

section qm

theorem map_qminor {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminor E a b u) = qminor (fun p q => φ (E p q)) a b u := by
  unfold qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext l
  simp only [Function.comp_apply, Tm, map_add]
  congr 1
  split_ifs <;> simp

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {n n' t : ℕ} (E : Fin n' → Fin n' → A) (ι : Fin n → Fin n')
    (hι : Function.Injective ι) (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun p q => E (ι p) (ι q)) a b u = qminor E (ι ∘ a) (ι ∘ b) u := by
  unfold qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  congr 1
  funext l
  simp only [Function.comp_apply, Tm]
  congr 1
  by_cases h : a (σ l) = b l
  · rw [if_pos h, if_pos (congrArg ι h)]
  · rw [if_neg h, if_neg (fun e => h (hι e))]

end qm

section main

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)

theorem gauge_last (c : Fin r → ℂ) :
    (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1)) =
      ∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) :=
  Finset.prod_congr rfl fun a _ => if_pos a.isLt

theorem resG_last (J : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) :
    Q.resG k r (Fin.last r) J c g = ((∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) • J (wCell k r (Fin.last r) c * g) := by
  unfold Q.resG
  rw [gauge_last]

theorem root_vector_action_cutoff (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleE) {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : a.val < b.val) :
    ((EA hD (eI k r a) (eI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (eI k r a)) (cI (eI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (eI k r a) (eI k r b) (cut k r 0 D f) g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

end main

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfParts
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def PStdOfParts : Prop := KB.RadHead → KB.HeadTop → FormOne → ZetaNormExists → KB.PStd

theorem pStdOfParts : PStdOfParts := fun hRH hHT hOne hZN hP =>
  pStd_of hRH hHT hOne hZN
    (fun Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw => by
      have hPc : P5.ThmPActualCpt := by
        intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        obtain ⟨K, h1, h2, h3, h4⟩ := hP Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        exact ⟨K, h1, h2, h3, fun F ε hε hF _ hG => h4 F ε hε hF hG⟩
      exact topContOn_of hPc hHT Wp Wq P p F w h h' hh hh' Cb hθ hF hw) hP

theorem pStd_cpt_of_parts (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) (hOne : FormOne)
    (hZN : ZetaNormExists) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  pStd_of_cpt hP hRH hHT hOne hZN (topContOn_of hP hHT)

end Formalism.FourierDecayAlt.P.PBO
end
end

