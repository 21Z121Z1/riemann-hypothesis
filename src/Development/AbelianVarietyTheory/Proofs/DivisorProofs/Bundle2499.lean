import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeTwoMulPadicValIntDiscr
section
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.RootDiscrExp

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem finrank_le_two_mul_padicValInt_discr (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (hp : p.Prime) (hd : (p : ℤ) ∣ discr E) : Module.finrank ℚ E ≤ 2 * padicValInt p (discr E) := by
  classical
  have := Fact.mk hp
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have ha : padicValInt p (discr E) = a := by
    rw [padicValInt, hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hm
    have h1 := Int.natCast_dvd.1 hd
    rwa [hdisc, pow_zero, one_mul] at h1
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨P, hPmax, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hP : P.IsPrime := hPmax.isPrime
  have hpP : (p : 𝓞 E) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPo.over]
      exact Ideal.mem_span_singleton_self _
    rwa [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  have h := diffExp E p a m hp hm hdisc P hP hpP
  have hpos := count_span_pos E p hp hP hpP
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hI0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := span_nat_ne_bot p
  have hdvd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ differentIdeal ℤ (𝓞 E) := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact pow_multiplicity_dvd _ _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) p ((Submodule.mem_bot _).1 hpP)
  have fD := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 hP) hD0
  have hd' := fD.le_multiplicity_of_pow_dvd hdvd
  have hc : ∀ X : Ideal (𝓞 E), X ≠ ⊥ → (normalizedFactors X).count P = multiplicity P X := fun X hX =>
    (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 E)).count_normalizedFactors_eq_multiplicity hX
  rw [hc _ hD0, hc _ hI0] at h
  rw [hc _ hI0] at hpos
  rw [ha]
  generalize multiplicity P (differentIdeal ℤ (𝓞 E)) = k at h hd'
  generalize multiplicity P (Ideal.span {(p : 𝓞 E)}) = e at h hd' hpos
  generalize Module.finrank ℚ E = n at h ⊢
  have hk : k ≠ 0 := by
    rintro rfl
    have : a * e ≠ 0 := mul_ne_zero ha0 hpos.ne'
    apply this
    nlinarith
  have hek : e ≤ 2 * k := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  nlinarith [Nat.mul_le_mul_left n hek]

theorem half_le_delta_two_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type)
    [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ →
    (1 / 2 : ℝ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E 2 := by
  intro E _ _ _ _ I _ d φ h
  have h1 := finrank_le_two_mul_padicValInt_discr E 2 Nat.prime_two (by exact_mod_cast h.2.2.2.2.1)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h2 : (Module.finrank ℚ E : ℝ) ≤ 2 * (padicValInt 2 (discr E) : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp, le_div_iff₀ hn]
  linarith

end GlobalTheory.RootDiscrExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsMonoTensorEffective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TensMul

variable {K : Type} [Field K] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of K))

def mulSec {L D : LB Y} (s : LB.Sec D) (σ : LB.Sec L) : LB.Sec (tens L D) where
  f := fun p : L.ι × D.ι => rs Y (inf_le_left : L.U p.1 ⊓ D.U p.2 ≤ L.U p.1) (σ.f p.1) *
      rs Y (inf_le_right : L.U p.1 ⊓ D.U p.2 ≤ D.U p.2) (s.f p.2)
  compat := fun (p q : L.ι × D.ι) => by
    obtain ⟨i, j⟩ := p
    obtain ⟨k, l⟩ := q
    have c₁ : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U i ⊓ L.U k :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have c₂ : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ D.U j ⊓ D.U l :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have h₁ : rs Y (inf_le_left : L.U i ⊓ L.U k ≤ L.U i) (σ.f i) =
        (L.g i k).val * rs Y (inf_le_right : L.U i ⊓ L.U k ≤ L.U k) (σ.f k) := σ.compat i k
    have h₂ : rs Y (inf_le_left : D.U j ⊓ D.U l ≤ D.U j) (s.f j) =
        (D.g j l).val * rs Y (inf_le_right : D.U j ⊓ D.U l ≤ D.U l) (s.f l) := s.compat j l
    have h₁' := congrArg (rs Y c₁) h₁
    have h₂' := congrArg (rs Y c₂) h₂
    rw [map_mul, rs_rs, rs_rs] at h₁' h₂'
    change rs Y (inf_le_left : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U i ⊓ D.U j)
        (rs Y (inf_le_left : L.U i ⊓ D.U j ≤ L.U i) (σ.f i) * rs Y (inf_le_right : L.U i ⊓ D.U j ≤ D.U j) (s.f j)) =
      (rs Y c₁ (L.g i k).val * rs Y c₂ (D.g j l).val) *
        rs Y (inf_le_right : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U k ⊓ D.U l)
          (rs Y (inf_le_left : L.U k ⊓ D.U l ≤ L.U k) (σ.f k) * rs Y (inf_le_right : L.U k ⊓ D.U l ≤ D.U l) (s.f l))
    rw [map_mul, map_mul, rs_rs, rs_rs, rs_rs, rs_rs, h₁', h₂']
    ring

def mulLin {L D : LB Y} (s : LB.Sec D) : SecOnR f L ⊤ →ₗ[K] SecOnR f (tens L D) ⊤ :=
  GlobalTheory.VeryAmpleGrowth.linTop f (fun a => mulSec s (SecOnR.topEquiv f L a))
    (fun a b (p : L.ι × D.ι) => by
      change @Eq Γ(Y, L.U p.1 ⊓ D.U p.2) (rs Y _ ((SecOnR.topEquiv f L (a + b)).f p.1) * rs Y inf_le_right (s.f p.2))
        (rs Y inf_le_left ((SecOnR.topEquiv f L a).f p.1) * rs Y inf_le_right (s.f p.2) +
          rs Y inf_le_left ((SecOnR.topEquiv f L b).f p.1) * rs Y inf_le_right (s.f p.2))
      rw [GlobalTheory.VeryAmpleGrowth.top_add, map_add]
      exact add_mul _ _ _)
    (fun c a (p : L.ι × D.ι) => by
      change @Eq Γ(Y, L.U p.1 ⊓ D.U p.2) (rs Y inf_le_left ((SecOnR.topEquiv f L (c • a)).f p.1) * rs Y inf_le_right (s.f p.2))
        (cst f (L.U p.1 ⊓ D.U p.2) c * (rs Y (inf_le_left : L.U p.1 ⊓ D.U p.2 ≤ L.U p.1) ((SecOnR.topEquiv f L a).f p.1) *
          rs Y (inf_le_right : L.U p.1 ⊓ D.U p.2 ≤ D.U p.2) (s.f p.2)))
      rw [GlobalTheory.VeryAmpleGrowth.top_smul, map_mul, rs_cst]
      exact _root_.mul_assoc _ _ _)

theorem top_mulLin {L D : LB Y} (s : LB.Sec D) (a : SecOnR f L ⊤) :
    SecOnR.topEquiv f (tens L D) (mulLin f s a) = mulSec s (SecOnR.topEquiv f L a) :=
  GlobalTheory.VeryAmpleGrowth.top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral Y] {L D : LB Y} (hL : L.IsLB) (s : LB.Sec D) {x : Y}
    (hx : x ∈ Out.nonzeroLocus s) : Function.Injective (mulLin f (L := L) s) := by
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hxL : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hxL
  let W : Y.Opens := L.U i₀ ⊓ Y.basicOpen (s.f j₀)
  have hWB : W ≤ Y.basicOpen (s.f j₀) := inf_le_right
  have hBD : Y.basicOpen (s.f j₀) ≤ D.U j₀ := Y.basicOpen_le _
  have hWL : W ≤ L.U i₀ := inf_le_left
  have hWT : W ≤ L.U i₀ ⊓ D.U j₀ := le_inf hWL (hWB.trans hBD)
  haveI : Nonempty W := ⟨⟨x, hi₀, hj₀⟩⟩
  have hu : IsUnit (rs Y (hWB.trans hBD) (s.f j₀)) := by
    rw [← rs_rs hBD hWB]
    exact (Y.toRingedSpace.isUnit_res_basicOpen (s.f j₀)).map _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : (mulSec s (SecOnR.topEquiv f L a)).f (i₀, j₀) = 0 := by
    have e := top_mulLin f s a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (tens L D) => σ.f (i₀, j₀)) e).symm.trans
      (GlobalTheory.VeryAmpleGrowth.top_zero f (M := tens L D) (i₀, j₀))
  have h' := congrArg (rs Y hWT) h
  change rs Y hWT (rs Y (inf_le_left : L.U i₀ ⊓ D.U j₀ ≤ L.U i₀) ((SecOnR.topEquiv f L a).f i₀) *
    rs Y (inf_le_right : L.U i₀ ⊓ D.U j₀ ≤ D.U j₀) (s.f j₀)) = rs Y hWT 0 at h'
  rw [map_mul, map_zero, rs_rs, rs_rs, hu.mul_left_eq_zero] at h'
  exact GlobalTheory.VeryAmpleGrowth.top_ext f fun k =>
    (GlobalTheory.SecGrowth.sec_eq_zero (M := L) (SecOnR.topEquiv f L a) (k₀ := i₀) hWL h' k).trans
      (GlobalTheory.VeryAmpleGrowth.top_zero f k).symm

end GlobalTheory.TensMul

theorem GlobalTheory.TensMul.finite_finrank_le_tens : ∀ {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) {L D : LB Y}, L.IsLB → D.IsLB → ∀ (s : LB.Sec D) {x : Y}, x ∈ Out.nonzeroLocus s → Module.Finite K (SecOnR f (tens L D) ⊤) → Module.Finite K (SecOnR f L ⊤) ∧ Module.finrank K (SecOnR f L ⊤) ≤ Module.finrank K (SecOnR f (tens L D) ⊤) := by
  intro K _ Y _ f L D hL _ s x hx hfin
  have hinj := GlobalTheory.TensMul.mulLin_injective f hL s hx
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackLeMulTwistDominantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_sections_pullback_le_mul_twist_of_dominant : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) [IsDominant f], IsProjOver p → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → (∀ x, (∀ j, co j x = 0) → x = 0) → ∀ (A : LB W), A.IsLB → ∀ (t : A.Sec), t ≠ 0 → (∀ (y : W) (i : A.ι) (hi : y ∈ A.U i) (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (fnOf _ (gen_mem hi) (t.f i) * co j (fnOf (f ⁻¹ᵁ V') h z))) → ∀ (B : LB W), B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤ r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  first | exact @GlobalTheory.Cartier.PullCount.finrank_sections_pullback_le_mul_twist_dominant | exact GlobalTheory.Cartier.PullCount.finrank_sections_pullback_le_mul_twist_dominant | (intros; apply GlobalTheory.Cartier.PullCount.finrank_sections_pullback_le_mul_twist_dominant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernEqSumCupInvariantForms
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolForm

theorem wedge_two_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (z : ⋀[K]^2 V)
    (h : ∀ f : Fin 2 → Module.Dual K V,
      exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) z = 0) : z = 0 := by
  by_contra hz
  obtain ⟨J, hJ⟩ := GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero
    (⇑(Module.finBasis K V).dualBasis) (Module.finBasis K V).dualBasis.span_eq z hz
  exact hJ (h _)

theorem pairingDual_ιMulti_two {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Fin 2 → Module.Dual K V) (u v : V) :
    exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 f) (exteriorPower.ιMulti K 2 ![u, v]) =
      f 0 u * f 1 v - f 0 v * f 1 u := by
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp
  ring

theorem ιMulti_two_swap {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] (u v : V) :
    exteriorPower.ιMulti K 2 ![u, v] = -exteriorPower.ιMulti K 2 ![v, u] := by
  have e : (![v, u] ∘ Equiv.swap (0 : Fin 2) 1) = ![u, v] := by
    ext i; fin_cases i <;> rfl
  rw [← e, AlternatingMap.map_swap _ _ (by decide)]

set_option maxHeartbeats 1000000 in

theorem chern_eq_sum_cup_form : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ → ∃ (I : Type) (_ : Fintype I) (c : I → primDR A) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))) (hω : ∀ k, Form.cl _ (ω k) ∈ primDR A), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (c k).1 (Form.cl _ (ω k))) ∧ ∀ f ∈ Fil A, ∀ x : HdR A, ψ f x = ∑ k, f (c k) * x ⟨_, hω k⟩ := by
  intro H K _ A _ g hA hg L hL ψ hψ
  obtain ⟨hFree, hHodge, -, -, hDual⟩ := H
  obtain ⟨-, hfin, -, -, e, he⟩ := hFree K A g hA hg
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hHodge K A g hA hg
  have hiso := (hDual K A g hA hg L hL ψ hψ).1
  obtain ⟨n, a, b, hch, rfl⟩ := hψ
  let pF := Submodule.projectionOnto (PrimitiveSubmodule A) N hN
  let pN := Submodule.projectionOnto N (PrimitiveSubmodule A) hN.symm
  have hsplit : ∀ c : primDR A, ((pF c : primDR A)) + (pN c : primDR A) = c :=
    Submodule.projection_add_projection_eq_self hN
  have hpN : ∀ c ∈ PrimitiveSubmodule A, pN c = 0 := fun c hc ↦
    (Submodule.projectionOnto_apply_eq_zero_iff hN.symm).2 hc

  have hvan : ∀ x y : Module.Dual K (primDR A),
      ∑ k, (x (pN (a k)) * y (pN (b k)) - x (pN (b k)) * y (pN (a k))) = 0 := by
    intro x y
    have hmem : ∀ z : Module.Dual K (primDR A), z ∘ₗ N.subtype ∘ₗ pN ∈ Fil A := fun z ↦
      (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by simp [hpN c hc]
    have := hiso _ (hmem x) _ (hmem y)
    rw [wedgeForm_apply] at this
    simpa using this
  have h0 : ∑ k, exteriorPower.ιMulti K 2
      ![((pN (a k) : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))), ((pN (b k) : primDR A) : FirstDeRham _)] = 0 := by
    haveI : FiniteDimensional K (FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := hfin
    apply wedge_two_eq_zero
    intro f
    rw [map_sum]
    simp only [pairingDual_ιMulti_two]
    exact hvan (f 0 ∘ₗ (primDR A).subtype) (f 1 ∘ₗ (primDR A).subtype)

  have hform : ∀ c : PrimitiveSubmodule A, ∃ w : Form (A.hom ≫ 𝟙 (Sp K)),
      Form.cl _ w = ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := fun c ↦ by
    have hc := c.2
    change ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    exact hc
  choose form hform using hform
  have hanti : ∀ u v : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) u v = -cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) v u := fun u v ↦ by
    rw [← he, ← he, ← map_neg, ιMulti_two_swap]
  have key : ∀ a₁ a₂ b₁ b₂ : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) (b₁ + b₂) =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) b₁ +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-b₂) a₁ + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) a₂ b₂ := by
    intro a₁ a₂ b₁ b₂
    simp only [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply]
    rw [hanti a₁ b₂]
    abel
  have hZ : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 = 0 := by
    rw [← map_zero e, ← h0, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (he _ _).symm
  obtain ⟨ω, hωdef⟩ : ∃ ω : Fin n ⊕ Fin n → Form (A.hom ≫ 𝟙 (Sp K)),
      ω = Sum.elim (fun k ↦ form (pF (b k))) (fun k ↦ form (pF (a k))) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : Fin n ⊕ Fin n → primDR A,
      c = Sum.elim a (fun k ↦ -(pN (b k) : primDR A)) := ⟨_, rfl⟩
  have hωl : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inl k)) = (pF (b k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inl, hform]
  have hωr : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inr k)) = (pF (a k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inr, hform]
  have hcl : ∀ k, c (Sum.inl k) = a k := fun k ↦ by rw [hcdef, Sum.elim_inl]
  have hcr : ∀ k, c (Sum.inr k) = -(pN (b k) : primDR A) := fun k ↦ by rw [hcdef, Sum.elim_inr]
  have hω : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω k) ∈ primDR A := fun k ↦ by
    rcases k with k | k
    · rw [hωl]; exact Subtype.property _
    · rw [hωr]; exact Subtype.property _
  have hsum : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (c k).1 (Form.cl _ (ω k)) =
      ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 := by
    have e3 : ∀ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (pF (b k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-(pN (b k) : primDR A).1) (pF (a k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 :=
      fun k ↦ by
      have ha := congrArg Subtype.val (hsplit (a k))
      have hb := congrArg Subtype.val (hsplit (b k))
      rw [Submodule.coe_add] at ha hb
      rw [← ha, ← hb]
      exact key _ _ _ _
    rw [Fintype.sum_sum_type]
    simp only [hcl, hcr, hωl, hωr, Submodule.coe_neg]
    rw [Finset.sum_congr rfl fun k _ ↦ e3 k, Finset.sum_add_distrib, Finset.sum_add_distrib, hZ,
      add_zero]
  refine ⟨Fin n ⊕ Fin n, inferInstance, c, ω, hω, by rw [hsum]; exact hch, ?_⟩
  intro f hf x
  rw [Fil, Submodule.mem_dualAnnihilator] at hf
  have hfF : ∀ c : PrimitiveSubmodule A, f c = 0 := fun c ↦ hf _ c.2
  have hfa : ∀ k, f (a k) = f (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add, hfF, zero_add]
  have hfb : ∀ k, f (b k) = f (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add, hfF, zero_add]
  have hxa : ∀ k, x (a k) = x (pF (a k)) + x (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add]
  have hxb : ∀ k, x (b k) = x (pF (b k)) + x (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add]
  have hxl : ∀ k, x ⟨_, hω (Sum.inl k)⟩ = x (pF (b k)) := fun k ↦
    congrArg x (Subtype.ext (hωl k))
  have hxr : ∀ k, x ⟨_, hω (Sum.inr k)⟩ = x (pF (a k)) := fun k ↦
    congrArg x (Subtype.ext (hωr k))
  have hv := hvan f x
  rw [wedgeForm_apply, Fintype.sum_sum_type]
  simp only [hxl, hxr, hcl, hcr, map_neg]
  simp only [hfa, hfb, hxa, hxb]
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hv]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.PolForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHoms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorsionTransfer

theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (m : ℕ) :
    (x ^ m).left = (x' ^ m).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem fixed_of_jointlyMonic : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro V W _ _ _ _ io F _ _ _ hF G _ H _ r hr hmono σ hσ m hfix x hx
  have hT : spMap σ.toRingHom ≫ (TF (R := W) F).hom = (TF (R := W) F).hom := by
    show Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext w
    exact hσ w
  have hV : (TF (R := W) F).hom ≫ spMap io = (TF (R := V) F).hom := by
    show (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext v
    exact hF v
  have hpb := isGrpPullback_pullback G (spMap io)
  let x' : TF (R := W) F ⟶ H := Over.homMk (spMap σ.toRingHom ≫ x.left) (by
    rw [Category.assoc, Over.w x]; exact hT)
  have key : ∀ k, x' ≫ r k = x ≫ r k := by
    intro k
    have hk := hr k
    let z := x ≫ r k
    have hs : z.left ≫ pullback.snd G.hom (spMap io) = (TF (R := W) F).hom := Over.w z
    let y : TF (R := V) F ⟶ G := Over.homMk (z.left ≫ pullback.fst G.hom (spMap io)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs]; exact hV)
    let ρ : (TF (R := W) F ⟶ H) →* (TF (R := W) F ⟶ (Over.pullback (spMap io)).obj G) :=
      MonoidHom.mk' (fun u => u ≫ r k) fun u v => MonObj.mul_comp u v (r k)
    have hzm : z ^ m = 1 := by
      have e := map_pow ρ x m
      rw [hx, map_one] at e
      exact e.symm
    have hym : y ^ m = 1 := by
      apply Over.OverMorphism.ext
      have e1 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl m
      rw [← map_pow, hzm, map_one] at e1
      have e0 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl 0
      simp only [pow_zero] at e0
      rw [e1, e0]
    have hfy := hfix y hym
    apply Over.OverMorphism.ext
    show (spMap σ.toRingHom ≫ x.left) ≫ (r k).left = x.left ≫ (r k).left
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact hfy
    · rw [Category.assoc, Category.assoc]
      change spMap σ.toRingHom ≫ z.left ≫ _ = z.left ≫ _
      rw [hs, hT]
  exact congrArg (fun u => u.left) (hmono _ x' x key)

end GlobalTheory.TorsionTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

attribute [local instance] Over.cartesianMonoidalCategory

theorem rel_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C (spMap ι ≫ z) (spMap ι ≫ p) := by
  intro E _ _ _ H Dw l Xo c Y X hFE C K K' _ _ ι z p hR
  obtain ⟨φ, k, hz, g, hs, hg, y, ψ, φ₁, f, t, t', hp, hf0, hx, hφ, hcomb⟩ := hR
  have hz' : ⊤ ≤ (spMap ι ≫ z) ⁻¹ᵁ X.F.U k := fun w _ => by
    exact hz (show spMap ι w ∈ (⊤ : (Sp K).Opens) from trivial)
  have hs' : (spMap ι ≫ z) ≫ X.π ≫ Y.s = spMap (ι.comp φ) := by
    rw [Category.assoc, hs, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨g', hg'⟩ := hFE K' (ι.comp φ) (spMap ι ≫ z) k hz' hs'
  have e : spMap ι ≫ (z ≫ X.π) = (spMap ι ≫ z) ≫ X.π := (Category.assoc _ _ _).symm
  have hv : ∀ τ i, g'.v τ i = spMap (dualMap ι) ≫ g.v τ i := fun τ i => by
    have h1 : g'.v τ i = (tv (GlobalTheory.FlagMod.tanPull ι e (X.F.vecAt k z hz rfl τ i))).left := by
      rw [hg' τ i, X.F.tanPull_vecAt k ι z hz hz' rfl rfl e]
    rw [h1, hg τ i]
    rfl
  refine ⟨ι.comp φ, k, hz', g', hs', hg', y, ι.comp ψ, φ₁, f, t, fun τ i => Units.map ι.toMonoidHom (t' τ i), ?_, hf0,
    ?_, ?_, fun τ i => ?_⟩
  · rw [hp, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [Category.assoc, hx, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [hφ]; rfl
  · obtain ⟨cf, h1, h2, h3⟩ := hcomb τ i
    refine ⟨fun j => ι (cf j), by simp [h1], fun j hj => by simp [h2 j hj], ?_⟩
    have h4 := GlobalTheory.LatDRFree.comb_map Y.t ι h3
    have hd : ∀ j, spMap (dualMap ι) ≫ spMap (dualMap ψ) ≫ f.v τ j = spMap (dualMap (ι.comp ψ)) ≫ f.v τ j := fun j => by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
      congr 2
      exact RingHom.ext fun a => by ext <;> simp [dualMap]
    simp only [hd] at h4
    rw [hv, ← e]
    exact h4

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAffineOpenUnitsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_affine_open_units : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))), Flat s →
    ∀ (W : M.Opens), IsAffineOpen W → Module.Flat ℤ Γ(M, W) ∧ IsUnit ((N : ℤ) : Γ(M, W)) := by
  first | exact @GlobalTheory.flat_and_isUnit_sections_of_flat_over_away | exact GlobalTheory.flat_and_isUnit_sections_of_flat_over_away | (intros; apply GlobalTheory.flat_and_isUnit_sections_of_flat_over_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesOfCloseLocalEquationClassicalPointStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generates_of_close_localEquation_classicalPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (x : M.Z) (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z), M.Cen U x y₀ → ∀ f, EqAt M D x f → ∃ k : ℕ, ∀ (G b : M₁.O (π x)), ‖M.val (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖M.val (gPt p ≫ y₀) f‖ → b ∈ Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} ^ k → (G : Ω) / f ∈ M.O x → (G : Ω) ≠ 0 ∧ f / G ∈ M.O x := by
  first | exact @GlobalTheory.Poinc.generates_of_close | exact GlobalTheory.Poinc.generates_of_close | (intros; apply GlobalTheory.Poinc.generates_of_close <;> assumption)
end

