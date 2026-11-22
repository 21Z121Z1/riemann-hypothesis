import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PolyArch

theorem roots_eig_any (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C) (w : ℂ)
    (hw : (minpoly G.F γ).eval₂ v.embedding w = 0) : ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v γ *ᵥ x = w • x := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ (γ ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ (γ ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF (γ ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) γ)
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F γ).natDegree => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hd0 : 0 < (minpoly G.F γ).natDegree := minpoly.natDegree_pos hint
  have hpm : (minpoly G.F γ).Monic := minpoly.monic hint
  set Q := (minpoly G.F γ).map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = (minpoly G.F γ).natDegree := by rw [hQ, hpm.natDegree_map]
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF γ) (minpoly G.F γ) = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = (minpoly G.F γ).natDegree - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F γ).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel hd0]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum
    ⟨(minpoly G.F γ).natDegree - 1, by omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKCx.PolyArch

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLatticeCohomologyVanish
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatCech

variable {ι : Type} [LinearOrder ι] {V : Type} [AddCommGroup V]
  (A : Cube.{0} ι ℤ) (φ : ∀ s : Finset ι, A.obj s →+ V)

def toFam (m : ℕ) (x : Cube.Term A m) : Finset ι → V :=
  fun s => if h : s.card = m then φ s (x ⟨s, h⟩) else 0

variable {A φ}

theorem toFam_zero (m : ℕ) : toFam A φ m 0 = 0 := by
  funext s; unfold toFam; split_ifs <;> simp

theorem nonempty_of_card {m : ℕ} (hm : 0 < m) {s : Finset ι} (h : s.card = m) : s.Nonempty :=
  Finset.card_pos.1 (by rw [h]; exact hm)

theorem delta_toFam {m : ℕ} (hm : 0 < m)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x)
    (x : Cube.Term A m) : DI.delta (toFam A φ m x) = toFam A φ (m + 1) (Cube.d A m x) := by
  funext t
  unfold DI.delta toFam
  by_cases ht : t.card = m + 1
  · rw [dif_pos ht, Cube.d_apply, map_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (t.erase i.1).card = m := by rw [Finset.card_erase_of_mem i.2, ht]; rfl
    rw [dif_pos hc, map_zsmul, hres _ _ _ (nonempty_of_card hm hc)]
  · rw [dif_neg ht]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ m := by
      have := Finset.card_pos.2 ⟨i, hi⟩
      rw [Finset.card_erase_of_mem hi]; omega
    rw [dif_neg hc, smul_zero]

theorem toFam_inCech {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) (x : Cube.Term A m) :
    DI.InCech N m (toFam A φ m x) := by
  refine ⟨?_, fun s => ?_, fun s hs => ?_⟩
  · unfold toFam; rw [dif_neg (by simp; omega)]
  · unfold toFam
    split_ifs with h
    · rw [← hrange s (nonempty_of_card hm h)]; exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · exact zero_mem _
  · unfold toFam; rw [dif_neg hs]

theorem toFam_injective {m : ℕ} (hm : 0 < m) (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    {x y : Cube.Term A m} (h : toFam A φ m x = toFam A φ m y) : x = y := by
  funext s
  have := congrFun h s.1
  unfold toFam at this
  rw [dif_pos s.2, dif_pos s.2] at this
  exact hinj _ (nonempty_of_card hm s.2) this

theorem exists_toFam {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) {c : Finset ι → V} (hc : DI.InCech N m c) :
    ∃ x : Cube.Term A m, toFam A φ m x = c := by
  have hex : ∀ s : {s : Finset ι // s.card = m}, ∃ y, φ s.1 y = c s.1 := fun s =>
    AddMonoidHom.mem_range.1 (by rw [hrange _ (nonempty_of_card hm s.2)]; exact hc.2.1 s.1)
  choose g hg using hex
  refine ⟨g, funext fun s => ?_⟩
  unfold toFam
  split_ifs with h
  · exact hg ⟨s, h⟩
  · exact (hc.2.2 s h).symm

theorem exact_iff_cechZero {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x) :
    Function.Exact (Cube.d A m) (Cube.d A (m + 1)) ↔ DI.CechZero N m := by
  have hm1 : 0 < m + 1 := Nat.succ_pos m
  constructor
  · intro hex c hc hdc
    obtain ⟨x, rfl⟩ := exists_toFam (A := A) hm1 hrange hc
    have hdx : Cube.d A (m + 1) x = 0 := toFam_injective (Nat.succ_pos _) hinj
      (by rw [← delta_toFam hm1 hres, hdc, toFam_zero])
    obtain ⟨y, hy⟩ := (hex x).1 hdx
    exact ⟨toFam A φ m y, toFam_inCech hm hrange y, by rw [delta_toFam hm hres, hy]⟩
  · intro hcz x
    constructor
    · intro hdx
      obtain ⟨y', hy'c, hy'd⟩ := hcz (toFam A φ (m + 1) x) (toFam_inCech hm1 hrange x)
        (by rw [delta_toFam hm1 hres, hdx, toFam_zero])
      obtain ⟨y, rfl⟩ := exists_toFam (A := A) hm hrange hy'c
      exact ⟨y, toFam_injective hm1 hinj (by rw [← delta_toFam hm hres, hy'd])⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d A m y

end GlobalTheory.LatCech

namespace GlobalTheory

theorem cechZero_latSec_iff_subsingleton_coh : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated]
    {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens), LatModel M F →
    (∀ i, IsAffineOpen (U i)) → (∀ i, genericPoint X ∈ U i) → ⨆ i, U i = ⊤ → ∀ b : ℕ, 0 < b →
    (DI.CechZero (fun s => latSec M (inter U s)) b ↔ Subsingleton (coh F b)) := by
  intro X _ hsepX V _ _ M F _ ι _ _ U hL hA hg hc b hb
  have hsep := (cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl hsepX) ι U hA
  obtain ⟨e, -⟩ := ((cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).2.1 ι U hc hsep).1
  have hO : ∀ s : Finset ι, cechOpen ⊤ U s = inter U s := fun s => by
    simp [cechOpen, inter, Finset.inf_eq_iInf]
  have hgen : ∀ s : Finset ι, genericPoint X ∈ cechOpen ⊤ U s := fun s => by
    rw [hO, ← SetLike.mem_coe, inter, Opens.coe_finset_inf]
    simp [hg]
  let φ : ∀ s : Finset ι, (cechCube ℤ F ⊤ U).obj s →+ V := fun s =>
    (hL.val (cechOpen ⊤ U s) (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).toAddMonoidHom
  have hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ s) := fun s _ =>
    (hL.inj _ (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).injective
  have hrange : ∀ s : Finset ι, s.Nonempty → (φ s).range = latSec M (inter U s) := by
    intro s _
    rw [← hO s, ← hL.range _ (hgen s)]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨(sectionsOn.toΓ F (cechOpen ⊤ U s)).symm z,
        congrArg (hL.val _ (hgen s)) ((sectionsOn.toΓ F (cechOpen ⊤ U s)).apply_symm_apply z)⟩
  have hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty →
      ∀ x, φ t (Cube.res (cechCube ℤ F ⊤ U) h x) = φ s x := by
    intro s t h _ x
    show hL.val _ _ (sectionsOn.toΓ F _ (sectionsOn.res ℤ F (cechOpen_anti ⊤ U h) x)) =
      hL.val _ _ (sectionsOn.toΓ F _ x)
    exact hL.res (cechOpen ⊤ U s) (cechOpen ⊤ U t) (cechOpen_anti ⊤ U h) (hgen t)
      (sectionsOn.toΓ F _ x)
  obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
  have e' := e F (p + 1)
  rw [show Subsingleton (coh F (p + 1)) ↔ Subsingleton (cechH ℤ F ⊤ U (p + 1)) from
    ⟨fun h => haveI := h; e'.injective.subsingleton,
      fun h => haveI := h; e'.symm.injective.subsingleton⟩,
    ← ModuleCat.isZero_iff_subsingleton, cechH_def, cech_def,
    ← HomologicalComplex.exactAt_iff_isZero_homology, cechComplex_exactAt_succ_iff]
  exact (LatCech.exact_iff_cechZero (φ := φ) (Nat.succ_pos p) hinj hrange hres).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserInvolution
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add' (G : HTGroup p) (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add, MulOpposite.unop_add]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem sh_sh' (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_of_sym (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have e : sh G ((β⁻¹ : G.Cˣ) : G.C) * β = 1 := by
    rw [← hβ, ← sh_mul', Units.mul_inv, sh_one']
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [e, one_mul]

end GlobalTheory.CentConj

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainBoundedAndSupProper
section
noncomputable section

open GlobalTheory.WeilM
open scoped TensorProduct

namespace GlobalTheory.HoweTrivial

theorem chain_bound_of_finiteLength {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule R M), StrictMono N → m ≤ L := by
  obtain ⟨h1, h2⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := R) (M := M))
  refine ⟨l + 1, fun m N hN => ?_⟩
  rcases m with _ | m
  · omega
  have h3 := Order.LTSeries.length_le_krullDim (LTSeries.mk m N hN)
  rw [← Module.coe_length, ← hl] at h3
  have h4 : m ≤ l := by exact_mod_cast h3
  omega

theorem sup_ne_top {H T : Type} [Group H] [AddCommGroup T] [Module ℂ T] (Θ : Representation ℂ H T)
    (h : IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule)
    (hc : ∀ N N' : Subrepresentation Θ, IsCoatom N → IsCoatom N' → N = N')
    (A B : Subrepresentation Θ) (hA : A ≠ ⊤) (hB : B ≠ ⊤) : A ⊔ B ≠ ⊤ := by
  obtain ⟨h1, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have hw : WellFoundedGT (Subrepresentation Θ) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).strictMono.wellFoundedGT
  have hco : IsCoatomic (Subrepresentation Θ) := inferInstance
  obtain ⟨C, hC, hAC⟩ := (eq_top_or_exists_le_coatom A).resolve_left hA
  obtain ⟨C', hC', hBC⟩ := (eq_top_or_exists_le_coatom B).resolve_left hB
  obtain rfl := hc C C' hC hC'
  exact ne_top_of_le_ne_top hC.1 (sup_le hAC hBC)

theorem trivial_irreducible (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ ℂ) this
  refine { eq_bot_or_eq_top := fun a => ?_ }
  rcases eq_bot_or_eq_top a.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem trivial_admissible (G : Type) [Group G] [TopologicalSpace G] :
    GlobalTheory.PRep.IsAdmissible (Representation.trivial ℂ G ℂ) := by
  refine ⟨fun v => ?_, fun K _ _ => inferInstance⟩
  simp

section

variable {Y G H T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup T] [Module ℂ T]

theorem mem_span_of_eq_zero (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsBigTheta om (Representation.trivial ℂ G ℂ) Θ p) (φ : SB Y) (hφ : p φ = 0) :
    (φ : Y → ℂ) ∈ Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} := by
  set A := Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} with hA
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  refine (hp.2.2 φ).1 hφ (f ∘ₗ A.mkQ ∘ₗ (SB Y).subtype) fun g ψ ψ₁ h => ?_
  have : A.mkQ (ψ₁ : Y → ℂ) = A.mkQ ψ := by
    rw [h]
    exact (Submodule.Quotient.eq A).2 (Submodule.subset_span ⟨g, ψ, ψ.2, rfl⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, this, Representation.trivial_apply]

def image (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsPairHom om (Representation.trivial ℂ G ℂ) Θ p) (N : Submodule ℂ (Y → ℂ))
    (hN : ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) : Subrepresentation Θ where
  toSubmodule := (N.comap (SB Y).subtype).map ((TensorProduct.lid ℂ T).toLinearMap ∘ₗ p)
  apply_mem_toSubmodule h := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨⟨om (1, h) φ, hom _ _ φ.2⟩, hN h _ hφ, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hp 1 h φ _ rfl]
    generalize p φ = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_image_iff (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsBigTheta om (Representation.trivial ℂ G ℂ) Θ p) (N : Submodule ℂ (Y → ℂ))
    (hA : Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N)
    (hN : ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) (φ : SB Y) :
    TensorProduct.lid ℂ T (p φ) ∈ (image om hom hp.1 N hN).toSubmodule ↔ (φ : Y → ℂ) ∈ N := by
  refine ⟨?_, fun h => ⟨φ, h, rfl⟩⟩
  rintro ⟨ψ, hψ, e⟩
  have e1 : p ψ = p φ := (TensorProduct.lid ℂ T).injective e
  have e2 : p (φ - ψ) = 0 := by rw [map_sub, e1, sub_self]
  have h3 := N.add_mem (hA (mem_span_of_eq_zero om hom hp _ e2)) hψ
  simpa using h3

end

theorem chain_bounded_and_sup_proper :
    ∀ {Y G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace Y]
    (om : G × H →* Module.End ℂ (Y → ℂ)), GlobalTheory.Published.HoweDualityFor om → (∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (Y → ℂ)), StrictMono N →
      (∀ i, Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N i ∧ N i ≤ SB Y ∧
        ∀ h, ∀ φ ∈ N i, om (1, h) φ ∈ N i) → m ≤ L) ∧
    ∀ N N' : Submodule ℂ (Y → ℂ),
      (Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N ∧ N ≤ SB Y ∧ ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) →
      (Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N' ∧ N' ≤ SB Y ∧ ∀ h, ∀ φ ∈ N', om (1, h) φ ∈ N') →
      N ≠ SB Y → N' ≠ SB Y → N ⊔ N' ≠ SB Y := by
  intro Y G H _ _ _ _ _ om hH hom
  obtain ⟨⟨T, _, _, Θ, p, hp, -, hfl, hco⟩, -⟩ :=
    hH ℂ (Representation.trivial ℂ G ℂ) (trivial_irreducible G) (trivial_admissible G)
  constructor
  · obtain ⟨L, hL⟩ := chain_bound_of_finiteLength hfl
    refine ⟨L, fun m N hN hs => hL m (fun i => Subrepresentation.subrepresentationSubmoduleOrderIso
      (image om hom hp.1 (N i) (hs i).2.2)) fun i j hij => ?_⟩
    refine (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).strictMono ?_
    have hlt := hN hij
    refine lt_of_le_of_ne ?_ fun e => hlt.not_ge fun φ hφ => ?_
    · exact Submodule.map_mono (Submodule.comap_mono hlt.le)
    · have h1 := (mem_image_iff om hom hp (N j) (hs j).1 (hs j).2.2 ⟨φ, (hs j).2.1 hφ⟩).2 hφ
      rw [← e] at h1
      exact (mem_image_iff om hom hp (N i) (hs i).1 (hs i).2.2 _).1 h1
  · have key : ∀ (N : Submodule ℂ (Y → ℂ))
        (hs : Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N ∧ N ≤ SB Y ∧
          ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N), N ≠ SB Y → image om hom hp.1 N hs.2.2 ≠ ⊤ := by
      intro N hs hne e
      refine hne (le_antisymm hs.2.1 fun φ hφ => ?_)
      refine (mem_image_iff om hom hp N hs.1 hs.2.2 ⟨φ, hφ⟩).1 ?_
      rw [e]
      exact Submodule.mem_top
    intro N N' hs hs' hne hne' e
    refine sup_ne_top Θ hfl hco _ _ (key N hs hne) (key N' hs' hne') ?_
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun t _ => ?_)
    obtain ⟨φ, hφ⟩ := hp.2.1 ((TensorProduct.lid ℂ T).symm t)
    have hm : (φ : Y → ℂ) ∈ N ⊔ N' := by rw [e]; exact φ.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hm
    have e1 : φ = (⟨a, hs.2.1 ha⟩ : SB Y) + ⟨b, hs'.2.1 hb⟩ := Subtype.ext hab.symm
    have e2 : t = TensorProduct.lid ℂ T (p ⟨a, hs.2.1 ha⟩) + TensorProduct.lid ℂ T (p ⟨b, hs'.2.1 hb⟩) := by
      rw [← map_add, ← map_add, ← e1, hφ, LinearEquiv.apply_symm_apply]
    rw [e2]
    exact Submodule.add_mem_sup ⟨_, ha, rfl⟩ ⟨_, hb, rfl⟩

end GlobalTheory.HoweTrivial

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependent
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charpoly_eq_of_monic_aeval_linearIndependent :
    ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K),
      P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 →
      LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  intro K _ n X P hP hdeg hX hli
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  have hc : X.charpoly.Monic := Matrix.charpoly_monic X
  have hcd : X.charpoly.natDegree = n := by
    simpa using Matrix.charpoly_natDegree_eq_dim X
  have hcdeg : X.charpoly.degree = n := by
    rw [Polynomial.degree_eq_natDegree hc.ne_zero, hcd]
  have hPdeg : P.degree = n := by
    rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdeg]
  have hDdeg : (X.charpoly - P).degree < n := by
    have h := Polynomial.degree_sub_lt (p := X.charpoly) (q := P)
      (by rw [hcdeg, hPdeg]) hc.ne_zero (by rw [hc.leadingCoeff, hP.leadingCoeff])
    rwa [hcdeg] at h
  have hDaeval : Polynomial.aeval X (X.charpoly - P) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hX, sub_zero]
  rw [← sub_eq_zero]
  by_contra hD0
  have hnat : (X.charpoly - P).natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hD0).mpr hDdeg
  have hsum : ∑ i : Fin n, (X.charpoly - P).coeff (i : ℕ) • X ^ (i : ℕ) = 0 := by
    have h := Polynomial.aeval_eq_sum_range' hnat X
    rw [hDaeval, Finset.sum_range (fun i => (X.charpoly - P).coeff i • X ^ i)] at h
    exact h.symm
  have hcoeff := Fintype.linearIndependent_iff.mp hli
    (fun i : Fin n => (X.charpoly - P).coeff (i : ℕ)) hsum
  apply hD0
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < n
  · exact hcoeff ⟨k, hk⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat (not_lt.mp hk))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRationalBoundedDenominators
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_rational_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (Ω : Set (AfP p)), IsCompact Ω → ∃ M : ℕ, 0 < M ∧ ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Ω → ∃ (k : ℤ) (e : ℕ), q * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  first | (exact @GlobalTheory.DenAway.den_bounded_of_isCompact) | (exact GlobalTheory.DenAway.den_bounded_of_isCompact) | (intros; apply GlobalTheory.DenAway.den_bounded_of_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieActionStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexifiedDerivedAction_isLieAction : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v v', SmoothVec (lieH Hm) σ v → SmoothVec (lieH Hm) σ v' → (∀ (a : ℂ) (Z Z' : Mt n), dRepC Hm σ (a • Z + Z') v = a • dRepC Hm σ Z v + dRepC Hm σ Z' v ∧ dRepC Hm σ Z (a • v + v') = a • dRepC Hm σ Z v + dRepC Hm σ Z v' ∧ dRepC Hm σ (Z * Z' - Z' * Z) v = dRepC Hm σ Z (dRepC Hm σ Z' v) - dRepC Hm σ Z' (dRepC Hm σ Z v)) ∧ (∀ X ∈ lieH Hm, dRepC Hm σ X v = dRep σ X v) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ Z, σ g (dRepC Hm σ Z v) = dRepC Hm σ (g * Z * g⁻¹) (σ g v)) ∧ ∀ Z, ⟪dRepC Hm σ Z v, v'⟫_ℂ = -⟪v, dRepC Hm σ (conjH Hm Z) v'⟫_ℂ := by
  first | exact @GlobalTheory.HolDict.LieAct.main | exact GlobalTheory.HolDict.LieAct.main | (intros; apply GlobalTheory.HolDict.LieAct.main <;> assumption)
end

