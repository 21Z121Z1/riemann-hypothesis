import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.RhoSpec
import Formalism.LocalToGlobal.IndefiniteReal.RowGSurj
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CongNormal
section
noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SS

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

variable (L n) in

def CongNormal : Prop :=
  ∀ (N : ℕ) (u κ : Formalism.AUTREP.GAf L n), u ∈ ReciprocityTheory.Aut.Umax L n → Formalism.L2.NG.Cong L n N κ →
    Formalism.L2.NG.Cong L n N (u * κ * u⁻¹)

def fixN (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (N : ℕ) : Submodule ℂ A where
  carrier := {a | ∀ κ, Formalism.L2.NG.Cong L n N κ → ρ κ a = a}
  zero_mem' := fun κ _ => map_zero _
  add_mem' := fun ha hb κ hκ => by rw [map_add, ha κ hκ, hb κ hκ]
  smul_mem' := fun c a ha κ hκ => by rw [map_smul, ha κ hκ]

structure UAdm (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ) : Prop where
  smooth : ∀ a, ∃ N : ℕ, 0 < N ∧ a ∈ fixN ρ N
  adm : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ (fixN ρ N)
  herm : ∀ x y, B y x = star (B x y)
  pos : ∀ x, x ≠ 0 → 0 < (B x x).re
  inv : ∀ g x y, B (ρ g x) (ρ g y) = B x y

def IsEqvA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (π : Formalism.L2.NG.FinTyp L n) (Φ : π.S →ₗ[ℂ] A) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), Φ ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ = ρ h (Φ f)

def isotA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (π : Formalism.L2.NG.FinTyp L n) : Submodule ℂ A :=
  ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ), LinearMap.range Φ

def SpanIsotA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) : Prop :=
  ∀ a : A, a ∈ ⨆ π : Formalism.L2.NG.FinTyp L n, isotA ρ π

def OrthIsotA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  ∀ π π' : Formalism.L2.NG.FinTyp L n, ¬ π.Iso π' → ∀ x ∈ isotA ρ π, ∀ y ∈ isotA ρ π', B x y = 0

end SS

end Formalism.IndefR.principalLevelFrame
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CutPassage3
section
namespace Formalism.IndefR.CxPass

theorem steps3 : Steps3 := fun _ _ _ _ _ _ _ _ _ _ _ _ I =>
  ⟨I.pRho, I.pJ, I.pRange, I.pMet_of I.pJt I.pJ, I.pFrames, I.pUni_of I.pJt I.pRho, I.pLat_of I.pJt,
    I.pGLat_of I.pJt I.pRho, I.pSand_of I.pJt I.pJ I.pRho I.pRange, fun _ _ _ _ _ _ τ => I.pGood_of I.pJt I.pRho τ⟩

theorem cutPassage3S : CutPassage3S := cutPassage3S_of_steps steps3

theorem cutPassage3 : CutPassage3 := cutPassage3_of_S cutPassage3S

end Formalism.IndefR.CxPass
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ExistsSumOfMemISup
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

section Spec

variable {K : Type} [Field K]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type} [Fintype ι]

theorem exists_sum_of_mem_iSup {R M : Type} [Ring R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι]
    (Q : ι → Submodule R M) {y : M} (hy : y ∈ ⨆ p, Q p) : ∃ ys : ι → M, (∀ p, ys p ∈ Q p) ∧ ∑ p, ys p = y := by
  classical
  refine Submodule.iSup_induction Q (motive := fun y => ∃ ys : ι → M, (∀ p, ys p ∈ Q p) ∧ ∑ p, ys p = y) hy ?_ ?_ ?_
  · intro i x hx
    refine ⟨Pi.single i x, fun p => ?_, ?_⟩
    · by_cases h : p = i
      · subst h; simpa using hx
      · simp [h]
    · simp [Finset.sum_pi_single']
  · exact ⟨0, fun _ => zero_mem _, by simp⟩
  · rintro x y ⟨xs, hxs, rfl⟩ ⟨ys, hys, rfl⟩
    exact ⟨xs + ys, fun p => add_mem (hxs p) (hys p), by simp [Finset.sum_add_distrib]⟩

def specOp (U : ι → Submodule ℂ E) (a : ι → ℂ) : Module.End ℂ E :=
  ∑ p, a p • ((U p).starProjection : E →L[ℂ] E).toLinearMap

theorem specOp_apply (U : ι → Submodule ℂ E) (a : ι → ℂ) (x : E) :
    specOp U a x = ∑ p, a p • (U p).starProjection x := by
  simp [specOp, LinearMap.sum_apply]

theorem proj_mem (U : ι → Submodule ℂ E) (p : ι) (x : E) : (U p).starProjection x ∈ U p := by
  exact Submodule.starProjection_apply_mem (U p) x

variable (U : ι → Submodule ℂ E) (hU : ∀ p q, p ≠ q → ∀ x ∈ U p, ∀ y ∈ U q, ⟪x, y⟫_ℂ = 0)
include hU

theorem proj_of_mem [DecidableEq ι] {p q : ι} {x : E} (hx : x ∈ U q) :
    (U p).starProjection x = if p = q then x else 0 := by
  split_ifs with h
  · subst h
    exact Submodule.starProjection_eq_self_iff.2 hx
  · have ho : x ∈ (U p)ᗮ := (Submodule.mem_orthogonal _ _).2 fun u hu => hU p q h u hu x hx
    have h1 := Submodule.starProjection_eq_self_iff.2 ho
    rw [Submodule.starProjection_orthogonal_val] at h1
    exact sub_eq_self.1 h1

theorem specOp_of_mem {a : ι → ℂ} {q : ι} {x : E} (hx : x ∈ U q) : specOp U a x = a q • x := by
  classical
  rw [specOp_apply]
  simp only [proj_of_mem U hU hx, smul_ite, smul_zero]
  simp

theorem proj_specOp (a : ι → ℂ) (q : ι) (x : E) :
    (U q).starProjection (specOp U a x) = a q • (U q).starProjection x := by
  classical
  rw [specOp_apply, map_sum, Finset.sum_eq_single q]
  · rw [map_smul, Submodule.starProjection_eq_self_iff.2 (proj_mem U q x)]
  · intro p _ hp
    rw [map_smul, proj_of_mem U hU (proj_mem U p x), if_neg (Ne.symm hp), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ q) h

theorem sum_proj {x : E} (hx : x ∈ ⨆ p, U p) : ∑ p, (U p).starProjection x = x := by
  classical
  refine Submodule.iSup_induction U (motive := fun x => ∑ p, (U p).starProjection x = x) hx ?_ ?_ ?_
  · intro q x hx
    simp only [proj_of_mem U hU hx]
    simp
  · simp
  · intro x y hx hy
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

omit hU in

theorem specOp_mem (a : ι → ℂ) (W : Submodule ℂ E) (hUW : ∀ p, U p ≤ W) (x : E) : specOp U a x ∈ W := by
  rw [specOp_apply]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hUW p (proj_mem U p x))

end Spec

section SpecW

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type} [Fintype ι]

theorem spec_eig (σ : K →+* ℂ) {H : Type} (P : ι → Submodule ℂ E) (W : Submodule ℂ E) (e : ι → H → K)
    (he : Function.Injective e) (hO : ∀ p q, p ≠ q → ∀ x ∈ P p ⊓ W, ∀ y ∈ P q ⊓ W, ⟪x, y⟫_ℂ = 0)
    (hS : (⨆ p, P p ⊓ W) = W) (c : ι) :
    P c ⊓ W = (⨅ T, LinearMap.ker (specOp (fun p => P p ⊓ W) (fun p => σ (e p T)) - σ (e c T) • LinearMap.id)) ⊓ W := by
  apply le_antisymm
  · intro x hx
    refine ⟨(Submodule.mem_iInf _).2 fun T => ?_, hx.2⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, specOp_of_mem (fun p => P p ⊓ W) hO hx]
    simp
  · rintro x ⟨hx, hW⟩
    have hT : ∀ T, specOp (fun p => P p ⊓ W) (fun p => σ (e p T)) x = σ (e c T) • x := fun T => by
      have h := (Submodule.mem_iInf _).1 hx T
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    have h0 : ∀ q, q ≠ c → (P q ⊓ W).starProjection x = 0 := by
      intro q hq
      obtain ⟨T, hTq⟩ : ∃ T, e q T ≠ e c T := by
        by_contra h
        push Not at h
        exact hq (he (funext h))
      have h1 := proj_specOp (fun p => P p ⊓ W) hO (fun p => σ (e p T)) q x
      rw [hT T, map_smul] at h1
      have h2 : (σ (e q T) - σ (e c T)) • (P q ⊓ W).starProjection x = 0 := by
        rw [sub_smul, ← h1, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (σ.injective (sub_eq_zero.1 h3)) hTq
      · exact h3
    have hx' : x ∈ ⨆ p, P p ⊓ W := by rw [hS]; exact hW
    have hsum := sum_proj (fun p => P p ⊓ W) hO hx'
    rw [Finset.sum_eq_single c (fun q _ hq => h0 q hq) (fun h => absurd (Finset.mem_univ c) h)] at hsum
    rw [← hsum]
    exact proj_mem (fun p => P p ⊓ W) c x

theorem spec_rat (σ : K →+* ℂ) {D : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (P : ι → Submodule ℂ E)
    (a : ι → K) (hO : ∀ p q, p ≠ q → ∀ x ∈ P p ⊓ LinearMap.range f, ∀ y ∈ P q ⊓ LinearMap.range f, ⟪x, y⟫_ℂ = 0)
    (hK : ∀ y : Fin D → K, y ∈ ⨆ p, (P p).comap (f.comp (cptL σ D))) :
    IsRat σ (relMat f (specOp (fun p => P p ⊓ LinearMap.range f) (fun p => σ (a p)) ∘ₗ f)) := by
  classical
  intro i k
  obtain ⟨ys, hys, hsum⟩ := exists_sum_of_mem_iSup _ (hK (Pi.single k 1))
  have hmem : ∀ p, f (cpt σ (ys p)) ∈ P p ⊓ LinearMap.range f := fun p => ⟨hys p, ⟨_, rfl⟩⟩
  have hcs : ∀ z : ι → Fin D → K, cpt σ (∑ p, z p) = ∑ p, cpt σ (z p) := fun z => by
    funext l
    simp [cpt, Finset.sum_apply]
  have hk : (Pi.single k 1 : Fin D → ℂ) = cpt σ (∑ p, ys p) := by
    rw [hsum]
    funext l
    by_cases h : l = k
    · subst h; simp [cpt]
    · simp [cpt, h]
  have key : (specOp (fun p => P p ⊓ LinearMap.range f) (fun p => σ (a p)) ∘ₗ f) (Pi.single k 1) =
      f (cpt σ (∑ p, a p • ys p)) := by
    rw [LinearMap.comp_apply, hk, hcs, map_sum, map_sum, hcs, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [specOp_of_mem (fun p => P p ⊓ LinearMap.range f) hO (hmem p), cpt_smul, map_smul]
  refine ⟨(∑ p, a p • ys p) i, ?_⟩
  simp only [relMat, Matrix.of_apply]
  rw [key, hf (solve_spec f (⟨_, rfl⟩ : f (cpt σ (∑ p, a p • ys p)) ∈ LinearMap.range f))]
  rfl

end SpecW

section Structs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {cr : Crd A fc} {b : Bool}

theorem rowsK (hW : (lv (fc X.zs) b).WF) (h3 : X.H3 cr b) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    y ∈ ⨆ p, X.Ep cr b p := by
  have hle : (⨆ p, (lv (fc X.zs) b).Qp Bs.μ0 p) ≤ ⨆ p, X.Ep cr b p :=
    iSup_mono fun p x hx => (X.mem_Ep cr b p x).2 ((h3 p x).1 hx)
  exact hle (hW.Qp_top ▸ Submodule.mem_top)

theorem liftsK (ht : (lv (fc X.zs) b).Types) (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (h5 : X.H5 cr b)
    (hr : X.RATth cr b) (h3W : X.H3W cr b) (j : Bs.J) (y : Fin (X.dW b j) → K) : y ∈ ⨆ p, X.WpK b j p := by
  obtain ⟨x, rfl⟩ := (X.liftMat_bij cr b hk he hn h5 hr j Bs.μ0).2 y
  have hx : x ∈ ⨆ p, (lv (fc X.zs) b).Zp j Bs.μ0 p := by
    rw [ht j]
    exact Submodule.mem_top
  have hle : (⨆ p, (lv (fc X.zs) b).Zp j Bs.μ0 p).map (X.liftMat cr b j Bs.μ0).mulVecLin ≤ ⨆ p, X.WpK b j p := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun p => Submodule.map_le_iff_le_comap.2 fun z hz => by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, X.mem_WpK b j p, X.key_lift cr b h5 hr j Bs.μ0 z]
      exact (h3W j p z).1 hz
  exact hle (Submodule.mem_map_of_mem hx)

theorem heckeRows_spec (h2 : X.H2 cr b) (hE : X.PartsE b) (hQ : ∀ y, y ∈ ⨆ p, X.Ep cr b p) (cf : ConvFace Bs) :
    Nonempty (X.HeckeRowsC cr b cf) := by
  have hO' : ∀ p q, p ≠ q → ∀ x ∈ X.EEp p ⊓ LinearMap.range (X.iC cr b Bs.μ0),
      ∀ y ∈ X.EEp q ⊓ LinearMap.range (X.iC cr b Bs.μ0), ⟪x, y⟫_ℂ = 0 := by
    rw [h2.2.2]
    exact hE.1
  refine ⟨{ hC := fun T => specOp (fun p => X.EEp p ⊓ X.EEl b) (fun p => Bs.v0.embedding (cf.ev p T)),
            maps := fun T e _ => specOp_mem _ _ _ (fun _ => inf_le_right) e,
            rat := fun T => ?_,
            eig := fun c => spec_eig Bs.v0.embedding X.EEp (X.EEl b) cf.ev cf.ev_inj hE.1 hE.2 c }⟩
  have h := spec_rat Bs.v0.embedding (X.iC cr b Bs.μ0) h2.1 X.EEp (fun p => cf.ev p T) hO' hQ
  rw [h2.2.2] at h
  exact h

theorem heckeW_spec (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (hP : X.PartsW b)
    (hK : ∀ j y, y ∈ ⨆ p, X.WpK b j p) (cf : ConvFace Bs) : Nonempty (X.HeckeWC b cf) :=
  ⟨{ hC := fun j T => specOp (fun p => X.Wp j p ⊓ LinearMap.range (X.w0C b j)) (fun p => Bs.v0.embedding (cf.ev p T)),
     maps := fun _ _ _ => specOp_mem _ _ _ (fun _ => inf_le_right) _,
     rat := fun j T => spec_rat Bs.v0.embedding (X.w0C b j) (X.principal_form_injective b hk he hn j) (X.Wp j) (fun p => cf.ev p T)
       (hP j).1 (hK j),
     eig := fun j c => spec_eig Bs.v0.embedding (X.Wp j) (LinearMap.range (X.w0C b j)) cf.ev cf.ev_inj (hP j).1 (hP j).2 c }⟩

end CxData

end Structs

section Fields3

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

theorem heckeRB_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false cf) :=
  CxData.heckeRows_spec (hR.what₂ false).1 (hR.partsE false)
    (CxData.rowsK (hR.rowHyp false).wf (hR.rowHyp false).h3) cf

theorem heckeRC_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true cf) :=
  CxData.heckeRows_spec (hR.what₂ true).1 (hR.partsE true)
    (CxData.rowsK (hR.rowHyp true).wf (hR.rowHyp true).h3) cf

theorem heckeWB_of (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (cf : ConvFace A3.fam3.base3) :
    Nonempty (X.HeckeWC false cf) :=
  CxData.heckeW_spec hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.partsW
    (CxData.liftsK hR.types0 hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W) cf

end Fields3

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open Formalism.L2.Theta

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem countable_GQ (V : HSp D) : Countable (GQ V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem borel_GA (V : HSp D) : BorelSpace (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem petPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) : PetPos V μ 𝓕 := by
  intro F hc hinv hne hint
  have := countable_GQ V
  have := measurableMul_GA V
  have := borel_GA V
  have := hH
  set U : Set (GA D V) := {g | F g ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUne : U.Nonempty := by
    by_contra h
    apply hne
    funext g
    by_contra hg
    exact h ⟨g, hg⟩
  have hUpos : 0 < μ U := hUo.measure_pos μ hUne
  have hnn : 0 ≤ᵐ[μ.restrict 𝓕] fun g => ‖F g‖ ^ 2 := ae_of_all _ (fun g => by positivity)
  refine lt_of_le_of_ne (integral_nonneg fun g => by positivity) ?_
  intro h0
  have hz : (fun g => ‖F g‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0.symm
  have hset : {g : GA D V | ¬ (‖F g‖ ^ 2 = (0 : GA D V → ℝ) g)} = U := by
    ext g
    simp [hUdef]
  have hFU : μ (U ∩ 𝓕) = 0 := by
    have h1 := ae_iff.1 hz
    rw [hset, Measure.restrict_apply hUo.measurableSet] at h1
    exact h1
  have key : U ≤ᵐ[μ] (⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) : Set (GA D V)) := by
    filter_upwards [hF.ae_covers] with x hx hxU
    obtain ⟨γ, hγ⟩ := hx
    refine Set.mem_iUnion.2 ⟨γ, ?_, ?_⟩
    · show F ((γ : GA D V) * x) ≠ 0
      rw [hinv _ γ.2 x]
      exact hxU
    · exact hγ
  have hU0 : μ U = 0 := by
    refine le_antisymm ((measure_mono_ae key).trans ?_) bot_le
    refine (measure_iUnion_le _).trans ?_
    simp only [measure_preimage_mul, hFU, tsum_zero, le_refl]
  exact hUpos.ne' hU0

end Formalism.IndefR.PeterssonHilbertSpace

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsBaseLevel
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

def indefiniteDataAtBaseLevel (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    IndefRows (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false) :=
  X.rowsOfR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.rowHyp false) hR.liftHyp0 (hR.pos false) hR.proviso0
    hR.types0 hR.h0
    (CxData.cutDims X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.wf false) hR.h4pos hR.kForm hR.ewNorm hR.types0
      (hR.what₂ false).1 (hR.ratMu false) (hR.rowHyp false).h3 hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W (hR.partsE false)
      hR.partsW hR.dimParts)

theorem subspaces_stable_in_block (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.zs.Stable ∧ X.zs.InBlock :=
  ⟨hR.stable, hR.inBlock⟩

end Formalism.IndefR.Cx
end
end

