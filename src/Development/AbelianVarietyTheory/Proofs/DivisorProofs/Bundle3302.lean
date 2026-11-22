import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3168
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3291
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2952
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3292
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToP
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

theorem kerPow_one {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) :
    KerPow f 1 k (1 : ptOver k k ⟶ A.X) := by
  refine ⟨⟨MonObj.one_comp _, one_pow _⟩, ?_⟩
  intro R _ _ x _ hx
  rw [pow_one] at hx
  subst hx
  refine ⟨Algebra.ofId k R, ?_, fun ψ _ => Subsingleton.elim _ _⟩
  change (spOver (Algebra.ofId k R) ≫ (1 : ptOver k k ⟶ A.X)).left = (1 : ptOver k R ⟶ A.X).left
  rw [MonObj.comp_one]

theorem exists_kerPow_primePow {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) (q e : ℕ) (hq : q.Prime) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f (q ^ e) H i ∧ ∃ j : ℕ, Module.finrank k H = q ^ j := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨G, -, ⟨tA⟩⟩ := GlobalTheory.AVTower.exists_tower q k A
  obtain ⟨G', -, ⟨tB⟩⟩ := GlobalTheory.AVTower.exists_tower q k B
  refine ⟨_, inferInstance, inferInstance, kerPt tA tB f e, kerPow_kerPt tA tB f e, ?_⟩
  exact (Nat.dvd_prime_pow hq).1 (finrank_quot_kerIdeal_dvd (tA.map tB f.hom) e) |>.imp fun _ h => h.2

theorem exists_kerPow_not_dvd : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B)
    (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  intro p hp k _ A B f m
  have hpp : p.Prime := hp.out
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow q n hq hn =>
    intro _ hdvd
    have hqp : q ≠ p := by
      rintro rfl
      exact hdvd (dvd_pow_self q hn.ne')
    obtain ⟨H, _, _, i, hi, j, hj⟩ := exists_kerPow_primePow f q n hq
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hj]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).1 (hpp.dvd_of_dvd_pow h)).symm
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    refine ⟨k, inferInstance, inferInstance, 1, kerPow_one f, ?_⟩
    rw [Module.finrank_self]
    exact hpp.not_dvd_one
  | coprime a b ha hb hab iha ihb =>
    intro _ hdvd
    have hpa : ¬ p ∣ a := fun h => hdvd (h.mul_right b)
    have hpb : ¬ p ∣ b := fun h => hdvd (h.mul_left a)
    obtain ⟨H₁, _, _, i₁, hi₁, h₁⟩ := iha (by omega) hpa
    obtain ⟨H₂, _, _, i₂, hi₂, h₂⟩ := ihb (by omega) hpb
    obtain ⟨H, _, _, i, hi, hH⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f a b hab H₁ i₁ H₂ i₂ hi₁ hi₂
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hH]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
    · exact h₁ h
    · exact h₂ h

end GlobalTheory.AV.KerPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_thetaExpansion_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  first | exact @GlobalTheory.Mum.exists_map_exp_all_traits | exact GlobalTheory.Mum.exists_map_exp_all_traits | (intros; apply GlobalTheory.Mum.exists_map_exp_all_traits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSectionStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_rule_section : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  first | exact @GlobalTheory.DetLine.PeriodFlat.exists_horizontal_section | exact GlobalTheory.DetLine.PeriodFlat.exists_horizontal_section | (intros; apply GlobalTheory.DetLine.PeriodFlat.exists_horizontal_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfKillsTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_id_pow_eq {K : Type} [Field K] (A : AbVar K) {T : Over (Sp K)} (x : T ⟶ A.X) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.comp_one]
  | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem exists_nsmul_eq_of_kills_torsion : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ),
    (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∃ g : A ⟶ C, f = n • g := by
  intro K _ A C f n hn hf
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h
    apply hn
    have : n = 0 := by exact_mod_cast h
    simp [this]
  obtain ⟨hiso, -⟩ := GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hn0
  have hiso' : IsIsogeny (n • 𝟙 A) := by rwa [natCast_zsmul] at hiso
  have hkill := GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints K A C f n hn hf
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel K A A C (n • 𝟙 A) f hiso' (fun T x hx => by
    apply hkill T x
    rw [nsmul_hom, id_hom, comp_id_pow_eq] at hx
    exact hx)
  refine ⟨g, ?_⟩
  rw [← hg, Preadditive.nsmul_comp, Category.id_comp]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_quasiInverse_isogeny : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    ∃ (n : ℕ) (g : B ⟶ A), 0 < n ∧ IsIsogeny g ∧ f ≫ g = n • 𝟙 A ∧ g ≫ f = n • 𝟙 B := by
  intro K _ A B f hf
  obtain ⟨hdim, -, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨n, hn, hker⟩ := GlobalTheory.T.abelianVariety_finiteHom_kernel_killed_by_nat K A B f hf.1
  have hB := B.smooth
  have hA := A.smooth
  rw [hdim] at hA
  obtain ⟨h, hh, hfh, hhf⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A.X B.X B.dim A.ab B.ab hA hB
    f.hom inferInstance n hn hker
  let g : B ⟶ A := Hom.mk (A := B) (B := A) h (h := hh)
  have e1 : f ≫ g = n • 𝟙 A := hom_ext (by simp [g, hfh])
  have e2 : g ≫ f = n • 𝟙 B := hom_ext (by simp [g, hhf])
  refine ⟨n, g, hn, ?_, e1, e2⟩
  have hm : IsIsogeny ((n : ℤ) • 𝟙 B) := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K B n (by exact_mod_cast hn.ne')).1
  rw [natCast_zsmul, ← e2] at hm
  exact (((GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K B A B g f hdim.symm hdim).1).mp hm).1

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimensionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_lowering_fibre_dimension : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) ≤ d) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, ∀ ℓ : ℕ, topologicalKrullDim ↥((Z \ NV P e 0 f) ∩ fib X ℓ) < d := by
  first | exact @GlobalTheory.HSAmp.exists_sec_fibre_dim_lt | exact GlobalTheory.HSAmp.exists_sec_fibre_dim_lt | (intros; apply GlobalTheory.HSAmp.exists_sec_fibre_dim_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveDiagonalLatticeMapTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.TraitOne

theorem factor_stalk (X : Scheme.{0}) (x : X) (V : Type) [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ X)
    (hx : ξ (IsLocalRing.closedPoint V) ⤳ x) :
    ∃ f : X.presheaf.stalk x →+* V, spMap f ≫ X.fromSpecStalk x = ξ := by
  refine ⟨(Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.stalkSpecializes hx).hom, ?_⟩
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hx
  conv_rhs => rw [← e1, ← e2]
  show Spec.map (CommRingCat.ofHom _) ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]
  rfl

theorem subset_abLocus {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real}
    {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) :
    (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro z hz
  obtain ⟨z', rfl⟩ : z ∈ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hz
  rw [abLocus_pullback (G' := (Over.pullback FinalForm.u₀).obj ρ.P.A) abLocusOne FinalForm.semi FinalForm.cart.1]
  intro K _ _ t _
  haveI := ρ.P.isAb.proper
  show IsProper (pullback.snd (pullback.snd ρ.P.A.hom FinalForm.u₀) t)
  infer_instance

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X), (∀ a b, ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧ IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR (m a b)) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ hA S ρ hBig M U₀ EE FinalForm hAdm hEE x hx u c pr hS R _ _ _ j hR hj G _ _ gm hgm
    D A U hLB hPsi m hm T ξ hξU hsp
  set ξR : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξR
  obtain ⟨hft, hpj⟩ := GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar o' Ω M x hx
  obtain ⟨-, p, hp, hpm⟩ := hpj R j hj
  obtain ⟨f, hf⟩ := factor_stalk M.Z x T.V ξ hsp
  obtain ⟨V', _, _, _, h, g', hc, hinj, hloc, hcomp, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f
  have heq : spMap g' ≫ ξR = spMap h ≫ ξ := by
    rw [hξR, ← hf, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp', hcomp]
  haveI : CharZero V' := (RingHom.charZero_iff hinj).1 inferInstance
  have hBV : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap h :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective h hinj
  let hK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') h hle
  have hKc : ∀ a, hK (algebraMap T.V _ a) = algebraMap V' _ (h a) := IsLocalization.map_eq hle
  have hjK : spMap hK ≫ jK T.V = jK V' ≫ spMap h := by
    show spMap hK ≫ spMap (algebraMap T.V (FractionRing T.V)) = spMap (algebraMap V' (FractionRing V')) ≫ spMap h
    rw [← spMap_comp', ← spMap_comp']
    congr 1
    ext a
    exact hKc a
  obtain ⟨ξ₀, hξ₀, hξ₀y⟩ := hξU
  set ξ' : Sp V' ⟶ M.Z := spMap g' ≫ ξR with hξ'
  have hξ₀' : (spMap hK ≫ ξ₀) ≫ U₀.ι = jK V' ≫ ξ' := by
    rw [Category.assoc, hξ₀, ← Category.assoc, hjK, Category.assoc, heq]
  have hsub := subset_abLocus FinalForm
  let w' : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  have hw'U : ξ' w' ∈ (U₀ : Set M.Z) := by
    have e1 : w' = jK V' (IsLocalRing.closedPoint (FractionRing V')) := by
      apply PrimeSpectrum.ext
      show (⊥ : Ideal V') = Ideal.comap (algebraMap V' (FractionRing V')) (IsLocalRing.closedPoint (FractionRing V')).asIdeal
      rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint (FractionRing V')).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).symm
    rw [e1]
    show (jK V' ≫ ξ') (IsLocalRing.closedPoint (FractionRing V')) ∈ (U₀ : Set M.Z)
    rw [← hξ₀']
    show U₀.ι ((spMap hK ≫ ξ₀) (IsLocalRing.closedPoint (FractionRing V'))) ∈ (U₀ : Set M.Z)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨D', A', U', hLB', hPsi'⟩ := FinalForm.unif V' inferInstance inferInstance hc ξ' ⟨w', hsub hw'U⟩
  have hG'semi : IsSemiAbelian ((Over.pullback ξ').obj FinalForm.G) := IsSemiAbelian.pullback ξ' FinalForm.G FinalForm.semi
  have hpb' := isGrpPullback_pullback FinalForm.G ξ'
  have h'' : IsGrpPullback ((Over.pullback (spMap g')).obj G) FinalForm.G ξ' (pullback.fst G.hom (spMap g') ≫ gm) :=
    (isGrpPullback_pullback G (spMap g')).comp hgm
  obtain ⟨e, he1, he2⟩ := grpPullback_iso hpb' h''
  haveI := he1
  set β : ((Over.pullback ξ').obj FinalForm.G).left ⟶ G.left := e.hom.left ≫ pullback.fst G.hom (spMap g') with hβdef
  have hβ : IsGrpPullback ((Over.pullback ξ').obj FinalForm.G) G (spMap g') β :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G (spMap g'))).congr (Category.id_comp _) rfl
  have hβgm : β ≫ gm = pullback.fst FinalForm.G.hom ξ' := by
    rw [hβdef, Category.assoc, he2]
  clear_value β
  have hGsemi : IsSemiAbelian G := by
    obtain ⟨e2, he21, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G ξR)
    haveI := he21
    exact GlobalTheory.isSemiAbelian_of_grpIso e2 (IsSemiAbelian.pullback ξR FinalForm.G FinalForm.semi)
  have hLBβ : LBIso U'.LG.L (U.LG.L.pull β) := by
    have h1 : LBIso (U.LG.L.pull β) (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ')) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hLB β hβgm.symm
    exact LBIso.trans U'.LG.isLB (pull_isLB FinalForm.L.isLB _) (pull_isLB U.LG.isLB _) hLB' (LBIso.symm h1)
  have hWo : IsOpen (ξR ⁻¹' (U₀ : Set M.Z)) := U₀.isOpen.preimage ξR.continuous
  have hPsiWo : ∀ y, PsiUnitOn D.toPre y (ξR ⁻¹' (U₀ : Set M.Z)) := fun y j' V hV hVW =>
    hPsi y j' V hV (hVW.trans (Set.preimage_mono hsub))
  have hker : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ ξR ⁻¹' (U₀ : Set M.Z) := by
    have e3 : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) = spMap g' w' :=
      PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g')
    show ξR _ ∈ (U₀ : Set M.Z)
    rw [e3]
    exact hw'U
  obtain ⟨ρ0, hsurj, hcoord, hequiv⟩ := GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr R hR G hGsemi D A U V' hBV inferInstance
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' g' β p hp hpm _ hWo hPsiWo hker hβ hLBβ
  obtain ⟨c', pr', hS', hmat⟩ := GlobalTheory.Poinc.Eq8.PullAlong.main g n _ _ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm V' hBV
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' ξ' (pullback.fst FinalForm.G.hom ξ') hpb' hLB' (spMap hK ≫ ξ₀) hξ₀'
  have hpt : (spMap hK ≫ ξ₀) ≫ FinalForm.u₀ ≫ u = spMap hK ≫ T.y := by
    rw [Category.assoc, hξ₀y]
  have key : ∀ (v : Sp (FractionRing V') ⟶ F.X), v = spMap hK ≫ T.y → ∀ c₁ pr₁, SharpBy F W A' v c₁ pr₁ →
      ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧
        Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G)
        (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr₁ a b f₁ →
        (Over.pullback (jK V')).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro v rfl c₁ pr₁ hS₁
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n _ _ F W hW T V' hBV inferInstance _ hG'semi D' A' U' h hK hloc hKc c₁ pr₁ hS₁
  obtain ⟨e8, hord, hrel⟩ := key _ hpt c' pr' hS'
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e8.toAddMonoidHom.comp ρ0, hinj, hirr _ T.irr, heq,
    e8.surjective.comp hsurj, ?_, ?_⟩
  · intro y r hr
    obtain ⟨⟨r', hr', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main V' D' inferInstance (ρ0 y)
    obtain ⟨h0, has⟩ := hord (ρ0 y) r' hr'
    exact ⟨h0, (hcoord y r r' hr hr').trans has⟩
  · intro a b y
    obtain ⟨f, fR, hMO, hfR, hcomm, hEC⟩ := hm a b
    haveI : IsMonHom f := hMO.1
    let f' : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G := (Over.pullback ξ').map f
    have hf'fst : f'.left ≫ pullback.fst FinalForm.G.hom ξ' = pullback.fst FinalForm.G.hom ξ' ≫ f.left := pullback.lift_fst _ _ _
    have hf' : IsMonHom f' := PullGtPf.isMonHom_of_grpPullback hpb' hpb' f f' hf'fst
    have hf'β : f'.left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc (f'.left ≫ β) ≫ gm = f'.left ≫ (β ≫ gm) := Category.assoc _ _ _
          _ = pullback.fst FinalForm.G.hom ξ' ≫ f.left := by rw [hβgm, hf'fst]
          _ = (β ≫ gm) ≫ f.left := by rw [hβgm]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, Category.assoc, hcomm]
      · calc (f'.left ≫ β) ≫ G.hom = f'.left ≫ (β ≫ G.hom) := Category.assoc _ _ _
          _ = ((Over.pullback ξ').obj FinalForm.G).hom ≫ spMap g' := by rw [hβ.1.w, ← Category.assoc, Over.w f']
          _ = β ≫ G.hom := hβ.1.w.symm
          _ = (β ≫ fR.left) ≫ G.hom := by rw [Category.assoc, Over.w fR]
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom V' hBV _ hG'semi D' A' U' f' hf'
    have hq := hequiv fR f' hfR hf' hf'β (m a b) m' hEC hm' y
    obtain ⟨f₁, hf₁, hf₁c⟩ := hmat a b f f' hMO hf'fst
    have hr := hrel a b f' f₁ m' hf' hf₁ hf₁c hm' (ρ0 y)
    simpa [hq] using hr

end GlobalTheory.Poinc.Eq8.TraitOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapEighthPowerSiegelModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_thMap_of_affine_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    IsReduced X → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U)) →
    ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hmu hn hred hP hA
  have hloc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3, h4⟩ := hA x
    exact GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine S G L ρ hL hρ g m n o X s q hmo hm3 hmu hn hP U h1 h2 h3 h4 x hxU
  choose W h hxW hs hT using hloc
  have hag : ∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ h i = y' ≫ h j := by
    intro i j K _ _ y y' e
    have hPK := hP K (y ≫ (W i).ι)
    obtain ⟨⟨θ, hθ⟩, -⟩ := gen_of_polFib S G L hL g K _ hPK
    have hmK : (m : K) ≠ 0 := by
      have := hmu.map (Spec.preimage (y ≫ (W i).ι ≫ s)).hom
      rw [map_natCast] at this
      exact this.ne_zero
    obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) K _ θ hmo hmK hn hPK
    have hH : HasTh G L ρ m ((y ≫ (W i).ι) ≫ q) c := ⟨θ, pt, hθ, hc⟩
    have h1 := hT i K y c (by rw [Category.assoc] at hH; exact hH)
    have h2 := hT j K y' c (by rw [e, Category.assoc] at hH; exact hH)
    refine CrdUniq.eq_of_pCrd ?_ h1 h2
    rw [Category.assoc, Category.assoc, hs, hs, ← Category.assoc, e, Category.assoc]
  have hcov : (⨆ x, W x) = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfi⟩ := GlobalTheory.ThetaGlue.glue_geom o n X s X W h hcov hs hag
  refine ⟨f, hf, fun K _ x c hH => ?_⟩
  let z : X := x.base (IsLocalRing.closedPoint K)
  have hr : Set.range x.base ⊆ Set.range (W z).ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact hxW z
  let x' : Sp K ⟶ (W z).toScheme := IsOpenImmersion.lift (W z).ι x hr
  have hx : x' ≫ (W z).ι = x := IsOpenImmersion.lift_fac _ _ _
  have h1 := hT z K x' c (by rw [← Category.assoc, hx]; exact hH)
  rw [← hx, Category.assoc, hfi]
  exact h1

theorem exists_thAt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ), P.g = 8 * g → GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) → rig.IsGen → Odd m → 3 ≤ m → IsUnit (m : cycAway n) → ∃ (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f := by
  intro g n hg hn hno F W hW P rig m hPg hSh hrig hmo hm3 hmu
  obtain ⟨hI, hN, hLN⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn hno F
  letI := P.isAb.comm
  have hpos : 0 < m ^ (4 * (8 * g)) := pow_pos (by omega) _
  have hA : ∀ x : F.X, ∃ U : F.X.affineOpens, x ∈ (U : F.X.Opens) ∧ IsDomain Γ(F.X, U) ∧ IsNoetherianRing Γ(F.X, U) ∧
      IsIntegrallyClosed Γ(F.X, U) ∧ CharZero Γ(F.X, U) := fun x => by
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp F.X.isBasis_affineOpens)
      (show x ∈ (⊤ : F.X.Opens) from trivial)
    have hne : (U : F.X.Opens) ≠ ⊥ := fun h => by simp [h] at hxU
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.affineOpen_ring_isDomain_noetherian_integrallyClosed F.X hI hN hLN ⟨U, hU⟩ hne
    exact ⟨⟨U, hU⟩, hxU, h1, h2, h3, GlobalTheory.SiegelTor.sFam_charZero_affineOpen g n F ⟨U, hU⟩ inferInstance⟩
  obtain ⟨f, hf, hT⟩ := exists_thMap_of_affine_cover F.X P.A P.L rig P.isLB hrig P.g m (m ^ (4 * (8 * g)) - 1) (cycAway n) F.X F.s (𝟙 F.X)
    hmo hm3 hmu (by rw [hPg]; omega) inferInstance (fun R _ x => by simpa using GlobalTheory.UMin.FibExist.polFib_of_point F.X P R x) hA
  exact ⟨_, f, hPg, hSh, hrig, hmo, hm3, hmu, by omega, hf, hT, hW⟩

end GlobalTheory.SiegTh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDimStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k), (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧ ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  first | exact @GlobalTheory.AVTower.exists_tower_and_height_eq | exact GlobalTheory.AVTower.exists_tower_and_height_eq | (intros; apply GlobalTheory.AVTower.exists_tower_and_height_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  first | exact @GlobalTheory.Poinc.Sep.TorPt.exists_torus_char | exact GlobalTheory.Poinc.Sep.TorPt.exists_torus_char | (intros; apply GlobalTheory.Poinc.Sep.TorPt.exists_torus_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTestModelBaseChangeCompletedLocStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedTestModel_baseChange_completedLocal : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε := by
  first | exact @GlobalTheory.Poinc.TestAtPt.exists_uTest_isBC | exact GlobalTheory.Poinc.TestAtPt.exists_uTest_isBC | (intros; apply GlobalTheory.Poinc.TestAtPt.exists_uTest_isBC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSpanPowPDivGroupLevelLeStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_span_pow_pDivGroup_level_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  first | exact @GlobalTheory.finrank_span_pow_le | exact GlobalTheory.finrank_span_pow_le | (intros; apply GlobalTheory.finrank_span_pow_le <;> assumption)
end

