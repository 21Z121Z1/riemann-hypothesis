import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeBaseChangeFree
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOps
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgebraActionBundleFiltrationStep
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

section Basic

variable {K A V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]

theorem apply_mem_idealV (τ : A →+* Module.End K V) {J : Ideal A} {a : A} (ha : a ∈ J) (v : V) :
    τ a v ∈ idealV τ J :=
  Submodule.mem_iSup_of_mem (⟨a, ha⟩ : J) (LinearMap.mem_range_self _ v)

theorem idealV_le (τ : A →+* Module.End K V) {J : Ideal A} {W : Submodule K V}
    (h : ∀ a ∈ J, ∀ v, τ a v ∈ W) : idealV τ J ≤ W :=
  iSup_le fun a => by
    rintro _ ⟨v, rfl⟩
    exact h a a.2 v

theorem apply_mem_of_mul_mem (τ : A →+* Module.End K V) {U J₁ : Ideal A} {t : A}
    (h : ∀ a ∈ U, a * t ∈ J₁) {μ : V} (hμ : μ ∈ idealV τ U) : τ t μ ∈ idealV τ J₁ := by
  have : idealV τ U ≤ (idealV τ J₁).comap (τ t) := idealV_le τ fun a ha v => by
    rw [Submodule.mem_comap]
    show τ t (τ a v) ∈ _
    rw [← Module.End.mul_apply, ← map_mul, mul_comm]
    exact apply_mem_idealV τ (h a ha) v
  exact this hμ

end Basic

section Coord

variable {K A V k : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V] [Field k]
  [Algebra k K] [Algebra k A]

theorem coord_vanish (τ : A →+* Module.End K V) {r : ℕ} (x : Fin r → V) (Θ : Fin r → V →ₗ[K] K)
    (l : A →ₗ[k] k)
    (hΘ : ∀ s s' a, Θ s (τ a (x s')) = if s = s' then algebraMap k K (l a) else 0)
    (hspan : ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)))
    {U : Ideal A} (hl : ∀ a ∈ U, l a = 0) (s : Fin r) {y : V} (hy : y ∈ idealV τ U) :
    Θ s y = 0 := by
  have : idealV τ U ≤ LinearMap.ker (Θ s) := idealV_le τ fun u hu v => by
    have h : Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)) ≤
        (LinearMap.ker (Θ s)).comap (τ u) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨a, s'⟩, rfl⟩
      show Θ s (τ u (τ a (x s'))) = 0
      rw [← Module.End.mul_apply, ← map_mul, hΘ, hl _ (U.mul_mem_right a hu)]
      simp
    exact h (hspan v)
  exact this hy

theorem exists_coords (τ : A →+* Module.End K V) {r : ℕ} (x : Fin r → V) (χ : A →ₐ[k] k)
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y)
    (hspan : ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)))
    (v : V) : ∃ d : Fin r → K, v - ∑ s, d s • x s ∈ idealV τ (RingHom.ker χ) := by
  have h : Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)) ≤
      Submodule.span K (Set.range x) ⊔ idealV τ (RingHom.ker χ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, s⟩, rfl⟩
    have ha : a - algebraMap k A (χ a) ∈ RingHom.ker χ := by
      simp [RingHom.mem_ker]
    have e : τ a (x s) = algebraMap k K (χ a) • x s + τ (a - algebraMap k A (χ a)) (x s) := by
      rw [map_sub, LinearMap.sub_apply, hc]
      abel
    show τ a (x s) ∈ _
    rw [e]
    exact Submodule.add_mem_sup
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)) (apply_mem_idealV τ ha _)
  obtain ⟨p, hp, μ, hμ, e⟩ := Submodule.mem_sup.1 (h (hspan v))
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hp
  refine ⟨d, ?_⟩
  rw [hd, ← e, add_sub_cancel_left]
  exact hμ

theorem exists_of_mem_idealV (τ : A →+* Module.End K V) {J₁ J : Ideal A} {t : A}
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y)
    (hJt : ∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) {y : V} (hy : y ∈ idealV τ J) :
    ∃ z, y - τ t z ∈ idealV τ J₁ := by
  have h : idealV τ J ≤ LinearMap.range (τ t) ⊔ idealV τ J₁ := idealV_le τ fun a ha v => by
    obtain ⟨c, hc'⟩ := hJt a ha
    have e : τ a v = τ t (algebraMap k K c • v) + τ (a - algebraMap k A c * t) v := by
      rw [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, hc, map_smul]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (apply_mem_idealV τ hc' v)
  obtain ⟨p, ⟨z, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (h hy)
  refine ⟨z, ?_⟩
  rw [← e, add_sub_cancel_left]
  exact hw

end Coord

section Local

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  {L : C.I → AddSubgroup V} {k A : Type} [Field k] [Algebra k K] [CommRing A] [Algebra k A]

theorem exists_local (τ : A →+* Module.End K V) {r : ℕ} (χ : A →ₐ[k] k) {J₁ J : Ideal A} {t : A}
    (l : A →ₗ[k] k) (hL : IsBun C L)
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y) {i : C.I}
    (hF : FreeAt C k τ L r i)
    (hJt : ∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁)
    (hmt : ∀ a ∈ RingHom.ker χ, a * t ∈ J₁) (hl : ∀ a ∈ J₁, l a = 0) (hlt : l t = 1) :
    ∃ P : V →ₗ[K] V, (∀ y ∈ idealV τ J, y - τ t (P y) ∈ idealV τ J₁) ∧
      (∀ w ∈ idealV τ J₁, P w = 0) ∧
      (∀ z, P (τ t z) - z ∈ idealV τ (RingHom.ker χ)) ∧
      ∀ y ∈ L i, P y ∈ L i := by
  obtain ⟨x, Θ', hx, hΘ', hint, hspan⟩ := hF
  have hΘ := hΘ' l
  set Θ := Θ' l with hΘdef
  have hW1 : ∀ s, ∀ w ∈ idealV τ J₁, Θ s w = 0 := fun s w hw =>
    coord_vanish τ x Θ l hΘ hspan hl s hw
  let P : V →ₗ[K] V := ∑ s, (Θ s).smulRight (x s)
  have hPa : ∀ y, P y = ∑ s, Θ s y • x s := fun y => by
    simp [P, LinearMap.sum_apply]
  have hΘT : ∀ s s', Θ s (τ t (x s')) = if s = s' then 1 else 0 := fun s s' => by
    rw [hΘ, hlt, map_one]
  have hP0 : ∀ w ∈ idealV τ J₁, P w = 0 := fun w hw => by
    rw [hPa]
    exact Finset.sum_eq_zero fun s _ => by rw [hW1 s w hw, zero_smul]

  have hPc : ∀ (d : Fin r → K) (y : V), y - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ →
      P y = ∑ s, d s • x s := fun d y hy => by
    have h1 : ∀ s, Θ s y = d s := fun s => by
      have h2 := hW1 s _ hy
      rw [map_sub, map_sum, sub_eq_zero] at h2
      rw [h2]
      simp [hΘT]
    rw [hPa]
    exact Finset.sum_congr rfl fun s _ => by rw [h1 s]
  have hT : ∀ z, ∃ d : Fin r → K, z - ∑ s, d s • x s ∈ idealV τ (RingHom.ker χ) ∧
      τ t z - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ := fun z => by
    obtain ⟨d, hd⟩ := exists_coords τ x χ hc hspan z
    refine ⟨d, hd, ?_⟩
    have := apply_mem_of_mul_mem τ hmt hd
    simpa [map_sub, map_sum] using this
  have hPT : ∀ z, P (τ t z) - z ∈ idealV τ (RingHom.ker χ) := fun z => by
    obtain ⟨d, h1, h2⟩ := hT z
    rw [hPc d _ h2, ← neg_sub]
    exact neg_mem h1
  refine ⟨P, fun y hy => ?_, hP0, hPT, fun y hy => ?_⟩
  · obtain ⟨z, hz⟩ := exists_of_mem_idealV τ hc hJt hy
    obtain ⟨d, -, h2⟩ := hT z
    have h3 : y - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ := by
      have := add_mem hz h2
      simpa using this
    rw [hPc d _ h3]
    simpa [map_sum] using h3
  · rw [hPa]
    exact sum_mem fun s _ => smul_mem_of_isBun C hL i (hint l s y hy) (hx s)

end Local

theorem subDeg_step : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (k A : Type) [Field k] [Algebra k K] [CommRing A] [Algebra k A] (τ : A →+* Module.End K V) (r : ℕ) (χ : A →ₐ[k] k) (J₁ J : Ideal A) (t : A) (l : A →ₗ[k] k), IsBun C L → (∀ a, IsHom C L L (τ a)) → (∀ (c : k) (x : V), τ (algebraMap k A c) x = algebraMap k K c • x) → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → (∀ i, FreeAt C k τ L r i) → J₁ ≤ J → t ∈ J → (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) → (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) → (∀ a ∈ J₁, l a = 0) → l t = 1 → subDeg C L (idealV τ J) = subDeg C L (idealV τ J₁) + deg C (quot C L (idealV τ (RingHom.ker χ))) := by
  intro K _ C V _ _ _ L k A _ _ _ _ τ r χ J₁ J t l hL hτ hc _ hF hJ ht hJt hmt hl hlt
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hW : idealV τ J₁ ≤ idealV τ J :=
    idealV_le τ fun a ha v => apply_mem_idealV τ (hJ ha) v
  choose P hP1 hP2 hP3 hP4 using fun i =>
    exists_local C τ χ l hL hc (hF i) hJt hmt hl hlt
  let g : idealV τ J →ₗ[K] V ⧸ idealV τ (RingHom.ker χ) :=
    (idealV τ (RingHom.ker χ)).mkQ ∘ₗ P i₀ ∘ₗ (idealV τ J).subtype
  have hg : ∀ y : idealV τ J, g y = Submodule.Quotient.mk (P i₀ y) := fun y => rfl
  have hgT : ∀ z, g ⟨τ t z, apply_mem_idealV τ ht z⟩ = Submodule.Quotient.mk z := fun z => by
    rw [hg]
    exact (Submodule.Quotient.eq _).2 (hP3 i₀ z)
  have hS : ShortExact C (sub C L (idealV τ J₁)) (sub C L (idealV τ J))
      (quot C L (idealV τ (RingHom.ker χ))) (Submodule.inclusion hW) g := by
    refine ⟨Submodule.inclusion_injective hW, fun y => ⟨fun h => ?_, ?_⟩, fun z => ?_,
      fun i x => Iff.rfl, fun i z => ⟨?_, ?_⟩⟩
    · rw [hg, Submodule.Quotient.mk_eq_zero] at h
      have h2 := hP1 i₀ y y.2
      have h3 := apply_mem_of_mul_mem τ hmt h
      have h4 : (y : V) ∈ idealV τ J₁ := by simpa using add_mem h2 h3
      exact ⟨⟨y, h4⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      rw [hg]
      show Submodule.Quotient.mk (P i₀ (w : V)) = 0
      rw [hP2 i₀ w w.2]
      simp
    · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨_, hgT z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨τ t z, apply_mem_idealV τ ht z⟩, hτ t i z hz, hgT z⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨P i y, hP4 i y hy, ?_⟩
      have h1 : P i₀ (y : V) = P i₀ (τ t (P i y)) := by
        have := hP2 i₀ _ (hP1 i y y.2)
        rwa [map_sub, sub_eq_zero] at this
      rw [hg, h1]
      exact ((Submodule.Quotient.eq _).2 (hP3 i₀ (P i y))).symm
  have hB := (SubQuot.isBun_sub_quot K C V L (idealV τ J) hL).1
  exact (deg_shortExact K C _ _ _ _ _ _ _ _ hB hS).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthColengthBound
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  first | exact @PositivityTheory.HtPt.Ra.cnt | exact PositivityTheory.HtPt.Ra.cnt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeBaseChangeFreeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_lattice_base_change_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.kerH R p τ (χ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeFibreIdealLocallyFreeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_lattice_fibre_ideal_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 (D.dId R p (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeGraphComapLocallyFreeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_lattice_graph_comap_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.stepKer | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.stepKer | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.stepKer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeKernelLocallyFreeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_lattice_kernel_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg restrictChart)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullExists

section Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => c k
  | .inr k => s (.inr k)

def secondChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k := fun k => s (.inr k)

theorem restrictChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    restrictChart (mixChart c s) = c := rfl

theorem secondChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    secondChart (mixChart c s) = secondChart s := rfl

theorem mseg_joinCoord {F : Type*} [CommMonoid F] (x : (Σ k, ι k) → F) (z : (Σ k, ι' k) → F)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (secondChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

end Charts

section Pull

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω₁}

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (secondChart s) := by
  rw [bcCoord, mseg_joinCoord]
  simp [mseg, map_prod]

theorem first_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg x (restrictChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem second_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg z (secondChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem ratio_first {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    (c : ∀ k, ι k) :
    algebraMap Ω Ω₁ (mseg x c / mseg x (restrictChart s)) ∈
      chartRing O (mseg (bcCoord x z)) s := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) s (mixChart c s)
  rw [mseg_bcCoord x z (mixChart c s), mseg_bcCoord x z s, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_right _ _ (second_ne_zero hs), ← map_div₀] at h
  exact h

theorem ratio_second {s t : ∀ k : K ⊕ K', Sum.elim ι ι' k} (ht : mseg (bcCoord x z) t ≠ 0) :
    mseg z (secondChart s) / mseg z (secondChart t) ∈ chartRing O (mseg (bcCoord x z)) t := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (mixChart (restrictChart t) s)
  rw [mseg_bcCoord x z (mixChart (restrictChart t) s), mseg_bcCoord x z t, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_left _ _
      ((map_ne_zero (algebraMap Ω Ω₁)).2 (first_ne_zero ht))] at h
  exact h

theorem map_mem_chartRing {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    {a : Ω} (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (bcCoord x z)) s).comap (IsScalarTower.toAlgHom O Ω Ω₁) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    exact ratio_first hs c
  exact hle ha

variable {N : ℕ} {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω₁ V₁]
  [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

def pullFam (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup V₁ := fun s =>
  spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))

theorem isLatFamily_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁) :
    IsLatFamily O (bcCoord x z) (pullFam x z E bc) := by
  refine ⟨fun s _ a ha v hv => LocFreeBC.smul_mem_spanOver _ _ ha hv,
    fun s t hs ht v hv => ?_⟩
  have hf : mseg (bcCoord x z) s / mseg (bcCoord x z) t ∈ chartRing O (mseg (bcCoord x z)) t :=
    div_mem_chartRing _ t s
  have hst : ∀ a ∈ chartRing O (mseg (bcCoord x z)) t, ∀ e ∈ pullFam x z E bc t,
      a • e ∈ pullFam x z E bc t := fun a ha e he => LocFreeBC.smul_mem_spanOver _ _ ha he
  have hfac : mseg (bcCoord x z) s / mseg (bcCoord x z) t =
      algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) *
        (mseg z (secondChart s) / mseg z (secondChart t)) := by
    rw [mseg_bcCoord x z s, mseg_bcCoord x z t, map_div₀, mul_div_mul_comm]
  change v ∈ AddSubgroup.closure _ at hv
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hv
    obtain ⟨m₁, hm₁⟩ := exists_pow_mul_mem_chartRing (mseg (bcCoord x z)) s t hs ha
    obtain ⟨m₂, hm₂⟩ := E.overlap _ _ (first_ne_zero hs) (first_ne_zero ht) e he
    refine ⟨m₁ + m₂, AddSubgroup.subset_closure ⟨_, mul_mem hm₁ (pow_mem
      (ratio_second (s := s) ht) m₂), _, ⟨_, hm₂, rfl⟩, ?_⟩⟩
    rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m₂) (bc e), smul_smul, smul_smul]
    congr 1
    rw [pow_add, map_pow]
    nth_rw 2 [hfac]
    rw [mul_pow]
    ring
  | zero => exact ⟨0, by simp⟩
  | add v w _ _ hv hw => exact LocFreeBC.loc_add _ _ hst hf hv hw
  | neg v _ hv =>
    obtain ⟨n, hn⟩ := hv
    exact ⟨n, by simpa using neg_mem hn⟩

theorem locFree_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁)
    (hbc : IsBaseChange Ω₁ bc) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (bcCoord x z) s ≠ 0) :
    LocFree (chartRing O (mseg (bcCoord x z)) s) N (pullFam x z E bc s) := by
  classical
  exact LocFreeBC.locFree_baseChange _ _ (fun _ ha => map_mem_chartRing hs ha) bc hbc N _
    (((BundleOfFamily.main O Ω K ι x N V).2 E).2 _ (first_ne_zero hs))

theorem exists_pullBC [IsDomain O] [IsDiscreteValuationRing O] (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  classical
  obtain ⟨EB, hEB⟩ := (BundleOfFamily.main O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1
    (pullFam x z E bc) (isLatFamily_pullFam E bc) (locFree_pullFam E bc hbc)
  refine ⟨EB, fun s hs => ?_⟩
  rw [hEB s hs]
  refine congrArg AddSubgroup.closure (Set.ext fun v => ?_)
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

end Pull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_,
    fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc => exists_pullBC E bc hbc⟩
  exact exists_pullBC (Ω₁ := Ω) (V₁ := V) (z := z) E LinearMap.id
    (IsBaseChange.ofEquiv (LinearEquiv.refl Ω V))

end GlobalTheory.CompanionTheory.Ar.Num.PullExists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparison
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ
  obtain ⟨Γ, Δ, hΓ, hΔ, hX⟩ := hQ
  obtain ⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V,
      F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂) := ⟨_, rfl⟩
  have memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s b
    subst hF
    exact Iff.rfl
  have hFlat : IsLatFamily O x F := by
    refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
    · have h := hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)
      rw [memF]
      simpa using h
    · obtain ⟨m, hm⟩ := hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)
      refine ⟨m, ?_⟩
      rw [memF]
      simpa using hm
  have hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s) := by
    intro s hs
    have hE := ((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).2 E).2 s hs
    have hC := ((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₂ V₂).2 C).2 s hs
    have hC' := ((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₂ V₂).2 C').2 s hs
    have h := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s)
      (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv)
      (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv)
      (fun w => (hΔ.2 s hs).2.2.1 w) (fun w hw => (hX s hs).2.1 w hw)).2
    rw [hF]
    exact h
  obtain ⟨E'', hE''⟩ := (GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).1 F hFlat hFfree
  have memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s hs b
    rw [hE'' s hs, memF]
  refine ⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_,
    ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1,
        (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩,
      (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩,
      fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((memE'' s hs w).1 hw)⟩⟩,
    ⟨Δ, ⟨hΔ.1, fun s hs => ⟨(hΔ.2 s hs).1, (hΔ.2 s hs).2.1, (hΔ.2 s hs).2.2.1,
        fun v hv => (memE'' s hs v).1 hv⟩⟩,
      fun s hs => ⟨fun v hv => (memE'' s hs v).2 hv, (hX s hs).2.1⟩⟩⟩
  · exact (memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)
  · exact ((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1

end GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleProduct
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.BundleOps

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N₁ V₁), ∃ P : ChartBundle O (mseg x) (N + N₁) (V × V₁), ∀ s, mseg x s ≠ 0 → P.lat s = (E.lat s).prod (F.lat s)) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (c : Ω), c ≠ 0 → ∃ E' : ChartBundle O (mseg x) N V, IsScaled x c E.lat E'.lat) ∧ (∀ (u : Ω) (a : K → ℤ), u ≠ 0 → ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x u a A.lat) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (t : Module.Basis (Fin N) Ω V), ∃ T : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ T.lat s ↔ ∀ i, t.repr v i ∈ chartRing O (mseg x) s) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∃ F : ChartBundle O (mseg x) N V₁, IsDualLat O x β E.lat F.lat) :=
  @PositivityTheory.Xgn.t_bundle_ops

end GlobalTheory.CompanionTheory.Ar.BundleOps
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersProperties
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem padicComplete_integers_structure : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C :=
  @PositivityTheory.HtPt.Twhopf.padic_alg

end GlobalTheory.CompanionTheory.Ar.HT
end

