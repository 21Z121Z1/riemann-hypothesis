import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.Bundle0001
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.EqNegOneOfJumpAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0573
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationUnitsMapEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NarrowLemmaOfCrystallineLubinTate
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PY.LocAlgCrys

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}

variable (L) in

def gal (g : GQ l) : ↥L.1 ⊗[ℚ_[l]] P.R.B →ₐ[↥L.1] ↥L.1 ⊗[ℚ_[l]] P.R.B :=
  Algebra.TensorProduct.map (AlgHom.id ↥L.1 ↥L.1) (P.actQ g : P.R.B →ₐ[ℚ_[l]] P.R.B)

variable (L) in

def phi (f : ℕ) : ↥L.1 ⊗[ℚ_[l]] P.R.B →ₐ[↥L.1] ↥L.1 ⊗[ℚ_[l]] P.R.B :=
  Algebra.TensorProduct.map (AlgHom.id ↥L.1 ↥L.1) (P.φB ^ f)

theorem mem_D (χ : ↥(GK K) →* (↥L.1)ˣ) (x : ↥L.1 ⊗[ℚ_[l]] P.R.B) :
    x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ↔ ∀ g : ↥(GK K), ((χ g : (↥L.1)ˣ) : ↥L.1) • gal P L g x = x := by
  have h : ∀ (g : ↥(GK K)) y, actVB (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) g y = ((χ g : (↥L.1)ˣ) : ↥L.1) • gal P L g y := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul v b =>
      change (((χ g : (↥L.1)ˣ) : ↥L.1) • v) ⊗ₜ[ℚ_[l]] (P.PD K).actB g b = _
      rw [P.PD_actB]
      rfl
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero, h]

theorem mul_mem_D {χ χ' : ↥(GK K) →* (↥L.1)ˣ} {x y : ↥L.1 ⊗[ℚ_[l]] P.R.B}
    (hx : x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ)) (hy : y ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ')) :
    x * y ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (χ * χ')) := by
  rw [mem_D] at hx hy ⊢
  intro g
  rw [map_mul, MonoidHom.mul_apply, Units.val_mul, ← smul_mul_smul_comm, hx, hy]

def Gen (f : ℕ) (χ : ↥(GK K) →* (↥L.1)ˣ) (c : (↥L.1)ˣ) : Prop :=
  Ideal.span {x | x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ∧ phi P L f x = (c : ↥L.1) • x} = ⊤

def Eig (f : ℕ) (χ : ↥(GK K) →* (↥L.1)ˣ) (c : (↥L.1)ˣ) : Prop :=
  ∀ x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ), phi P L f x = (c : ↥L.1) • x

variable {P} {f : ℕ} {χ χ' : ↥(GK K) →* (↥L.1)ˣ} {c c' : (↥L.1)ˣ}

theorem Gen.eig_inv (h1 : Eig P f (1 : ↥(GK K) →* (↥L.1)ˣ) 1) (h : Gen P f χ c) : Eig P f χ⁻¹ c⁻¹ := by
  intro y hy
  have key : ∀ x ∈ Ideal.span {x | x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ∧ phi P L f x = (c : ↥L.1) • x},
      x * ((c : ↥L.1) • phi P L f y - y) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have h2 := mul_mem_D P hx.1 hy
      rw [mul_inv_cancel] at h2
      have h3 := h1 _ h2
      rw [map_mul, hx.2, Units.val_one, one_smul] at h3
      rw [mul_sub, mul_smul_comm, ← smul_mul_assoc, h3, sub_self]
    | zero => rw [zero_mul]
    | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
  have h4 := key 1 (by rw [h]; trivial)
  rw [one_mul, sub_eq_zero] at h4
  conv_rhs => rw [← h4, smul_smul, Units.inv_mul, one_smul]

theorem Eig.gen {AI : LocAinf l P} (T : LocTied l P AI) (hc : IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ))
    (h : Eig P f χ c) : Gen P f χ c := by
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.TiedSpan.tied_crisSpan l P AI T (GlobalTheory.MemLoc.tied_regular_and_onto l P AI T).1
    K L ↥L.1 _ hc 1
  rw [Gen, Ideal.eq_top_iff_one, h1]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [GlobalTheory.TwistJump.map_mulLeft]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨hd i, h _ (hd i)⟩)

theorem phi_ιA (AI : LocAinf l P) (k : ℕ) (x : Ainf l) :
    (P.φB ^ k) (AI.ιA x) = AI.ιA (WittVector.map (iterateFrobenius _ l k) x) := by
  induction k with
  | zero =>
    change AI.ιA x = _
    congr 1
    ext i
    simp
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, ← AI.ιA_φ, WittVector.frobenius_eq_map_frobenius]
    congr 1
    ext i
    simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

variable (P) in

def Good (f : ℕ) (χ : ↥(GK K) →* (↥L.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥L.1) → ℤ) (c : (↥L.1)ˣ) : Prop :=
  IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ∧
    (∀ τ b, multV (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) τ b = if b = a τ then 1 else 0) ∧ Eig P f χ c

variable {AI : LocAinf l P} (T : LocTied l P AI) (h1 : Eig P f (1 : ↥(GK K) →* (↥L.1)ˣ) 1)
  {a a' : (↥K.1 →ₐ[ℚ_[l]] ↥L.1) → ℤ}
include T h1

theorem Good.inv (h : Good P f χ a c) : Good P f χ⁻¹ (-a) c⁻¹ :=
  ⟨(GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l P AI T K L χ a h.1 h.2.1).1, (GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l P AI T K L χ a h.1 h.2.1).2,
    (h.2.2.gen T h.1).eig_inv h1⟩

end Local

section Bridge

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  (P : LocPrime l) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
  {L L' : FinExt l} (hL : L.1 ≤ L'.1)

def tr : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] ↥L'.1 ⊗[ℚ_[l]] P.R.B :=
  LinearMap.rTensor P.R.B ((IntermediateField.inclusion hL).toLinearMap ∘ₗ LinearMap.proj 0)

variable (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) (χ : ↥(GK Bw.Kw) →* (↥L'.1)ˣ)
  (hχ : ∀ g, (((χ g : (↥L'.1)ˣ) : ↥L'.1) : Qbar l) = ent ψ (Bw.e.symm g))
include hχ

end Bridge

end GlobalTheory.PY.LocAlgCrys

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.SerSys.SuppTame

section Chain

open GlobalTheory.LocGL

theorem isIrreducible_of_isIrrRep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : IsIrrRep ρ) : ρ.IsIrreducible := by
  obtain ⟨hn, hW⟩ := h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hv ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · rcases hW S.toSubmodule (fun x w hw => S.apply_mem_toSubmodule x hw) with h0 | h1
    · exact Or.inl (Subrepresentation.ext (by rw [h0]; rfl))
    · exact Or.inr (Subrepresentation.ext (by rw [h1]; rfl))

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem hasSupport_zero (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {g : ℕ} [Fact g.Prime] {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) ℚ_[g]) V) (hs : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) : HasSupport π (0 : Multiset (IrrGL ℚ_[g])) := by
  obtain ⟨s, hs'⟩ := SupportRing.exists_hasSupport hZ (IrrGL.of π hs hi)
  have h1 : HasSupport π s := hs'.of_equiv (IrrGL.equivOf π hs hi).symm
  have h2 := h1.sum_fst
  rw [Fintype.card_fin] at h2
  have h3 : s = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
    have h4 := (h1.isCusp hy).1
    have h5 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hy)
    omega
  rwa [h3] at h1

theorem chain : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (g : ℕ) [Fact g.Prime] (π : Supp.GLRep g), IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ → ∃ (L : List (Supp.GLRep g)) (y : List (GlobalTheory.LocGL.IrrGL ℚ_[g])), Supp.InInd π L ∧ (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧ GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[g])) ∧ List.Forall₂ (fun (ρ : Supp.GLRep g) (x : GlobalTheory.LocGL.IrrGL ℚ_[g]) => ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (GlobalTheory.LocGL.IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
  intro hZ g _
  have H : ∀ (N : ℕ) (π : Supp.GLRep g), π.1 = N → IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ →
      ∃ (L : List (Supp.GLRep g)) (y : List (IrrGL ℚ_[g])), Supp.InInd π L ∧
        (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧
          GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ HasSupport π.2.ρ (y : Multiset (IrrGL ℚ_[g])) ∧
        List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL ℚ_[g]) =>
          ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro π hN hπ hs
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0
        refine ⟨[], [], Supp.InInd.nil π hN hπ, by simp, ?_, List.Forall₂.nil⟩
        obtain ⟨n, π⟩ := π
        simp only at hN
        subst hN
        exact hasSupport_zero hZ _ hs (isIrreducible_of_isIrrRep hπ)
      · obtain ⟨a, b, hab, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ :=
          GlobalTheory.JacFactor.exists_map_jac₂ ℚ_[g] π.1 _ π.2.ρ hs (isIrreducible_of_isIrrRep hπ) (hN ▸ hpos)
        have hM : Supp.MapsToProd π.2.ρ σ ρ := GlobalTheory.GLp.Supp.mapsToProd_of_jac₂ g a b π.1 hab _ _ _ π.2.ρ σ ρ φ hφ
        let σ' : Supp.GLRep g := ⟨a, Rep.of σ⟩
        let ρ' : Supp.GLRep g := ⟨b, Rep.of ρ⟩
        obtain ⟨Lσ, yσ, hI, hL, hS, hF⟩ :=
          ih a (by omega) σ' rfl (isIrrRep_of_isIrreducible hσi) hσs
        have hρsupp : HasSupport ρ {IrrGL.of ρ hρs hρi} :=
          (hasSupport_self (IrrGL.isCusp_of.2 ⟨hb, hρc⟩)).of_equiv (IrrGL.equivOf ρ hρs hρi).symm
        obtain ⟨μ₁, μ₂, h₁, h₂, hsupp⟩ := GlobalTheory.IndChain.SuppStep.supp_of_mapsToProd hZ g _ _ _ _ _ _ π.2.ρ σ ρ hs (isIrreducible_of_isIrrRep hπ) hM
          yσ {IrrGL.of ρ hρs hρi} hS hρsupp
        refine ⟨ρ' :: Lσ, (IrrGL.of ρ hρs hρi).tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂) ::
          yσ.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)), ?_, ?_, ?_, ?_⟩
        · exact Supp.InInd.cons π σ' ρ' Lσ hπ (isIrrRep_of_isIrreducible hρi) hI hM
        · exact List.forall_mem_cons.2 ⟨⟨hb, isIrrRep_of_isIrreducible hρi, hρs, hρi, hρc⟩, hL⟩
        · convert hsupp using 1
          rw [← Multiset.cons_coe, ← Multiset.map_coe, Multiset.map_singleton, add_comm, Multiset.singleton_add]
        · refine List.Forall₂.cons ⟨hρs, hρi, μ₂, h₂, rfl⟩ ?_
          refine List.forall₂_map_right_iff.2 (hF.imp fun ρ x ⟨hs, hi, hin⟩ => ⟨hs, hi, ?_⟩)
          exact IrrGL.inert_equivalence.trans hin ⟨μ₁, h₁, rfl⟩
  intro π hπ hs
  exact H _ π rfl hπ hs

end Chain

theorem supportCompat : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hZ hL D T I rc hrc k v π hi hs
  obtain ⟨L, y, hind, hsc, hsup, hf⟩ := chain hZ (D.host.g k) π hi hs
  refine ⟨L, hind, fun ρ hρ => ?_, ?_⟩
  · obtain ⟨h0, h1, -, -, h3⟩ := hsc ρ hρ
    exact ⟨h0, h1, GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal ℚ_[D.host.g k] ρ.1 _ ρ.2.ρ h3⟩
  show D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) =
    (L.map fun ρ => D.naut.inePol (rc k v ρ.1 ρ.2) (D.ntypes.tg k v)).prod
  rw [GlobalTheory.SuppIne.suppIne hL D T I rc hrc k v π y hsup]
  congr 1
  clear hsup hind hsc
  induction hf with
  | nil => rfl
  | cons h _ ih =>
    obtain ⟨hs', hi', hin⟩ := h
    rw [List.map_cons, List.map_cons, ih, GlobalTheory.TypeRec.TwistInert.inePol_inert hL D T I rc hrc k v _ hs' hi' _ hin]

end GlobalTheory.SerSys.SuppTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeFixedThetaVectorSchrodingerIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrime_fixedThetaVector_schrodinger_indicator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ p : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ p → ∀ (PP : Pl D.host.E), PP ∈ Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ x₀ : WO S T, IsHalf (cA D e) x₀ → (∀ a b, adjCo φ S T (frCo φ βS) (frCo φ βT) x₀ a b = if a.val = b.val then 1 else 0) → Shape ψ S T e (halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ 1) x₀ p := by
  first | exact @GlobalTheory.ThPShape.thPVec_shape | exact GlobalTheory.ThPShape.thPVec_shape | (intros; apply GlobalTheory.ThPShape.thPVec_shape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensions
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

set_option synthInstance.maxHeartbeats 200000 in

theorem sec_eq_zero_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  intro E _ _ _ H Dw l Xo c a n h hh hv
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_nonempty_comp E H Dw l Xo c
  funext p y
  show h p y = 0

  have key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m := by
    intro m hm
    letI : Field (p.R ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance
    haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)
    obtain ⟨w, hw⟩ := hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y
    have e := evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw
    rw [hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp e.symm

  have hj : h p y ∈ (⊥ : Ideal p.R).jacobson :=
    Ideal.mem_sInf.mpr fun J hJ => key J hJ.2
  have hrad : (⊥ : Ideal p.R).IsRadical := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact p.rad ⟨k, hk⟩
  rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad] at hj
  exact hj

end GlobalTheory.Reg
end

