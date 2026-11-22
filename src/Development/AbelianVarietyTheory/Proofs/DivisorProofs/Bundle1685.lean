import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceHeckeCharacterBoundedLevelTrivia
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.HeckeCont

open Formalism.L2.Host GlobalTheory.Mem.Col2.SplitChar

theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem eq_one_of_cong : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1 := by
  intro D χ S k hS hv
  refine ⟨(∏ q ∈ S, q) ^ k, pow_pos (Finset.prod_pos fun q hq => (hS q hq).pos) k, ?_⟩
  rintro u hu ⟨s, hs, e⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu) (fun w => ?_) (fun v x hx => ?_)
  · rw [finIdl_fst]
    rfl
  · have hU : Valued.v ((finIdl D u : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1 := finIdl_unit hu v
    have hxU : IsUnitAt v x := by
      show Valued.v (x : v.adicCompletion D.host.E) = 1
      rw [hx]
      exact hU
    rcases hv v with hunr | ⟨q, hq, hov, hlev⟩
    · exact hunr x hxU
    · refine hlev x hxU ?_
      rw [hx, vl_sub_one, e]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hP : OverP D.host (∏ q ∈ S, q) v := by
        show (((∏ q ∈ S, q : ℕ)) : 𝓞 D.host.E) ∈ v.asIdeal
        rw [hc, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hov
      have h1 := le_exp_neg_one_of_lt_one (val_nat_lt hP)
      rw [map_mul, Nat.cast_pow, map_pow]
      calc vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k * vl D v s ≤ vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k :=
            mul_le_of_le_one_right' (vl_le hs v)
        _ ≤ WithZero.exp (-1 : ℤ) ^ k := pow_le_pow_left₀ zero_le' h1 k
        _ = WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp

end GlobalTheory.HeckeCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledPairWeilDatumSchrodingerTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

theorem exists_dbl_weilDatum_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd ∧
          ∃ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco
  have h1 : Formalism.L2.Theta.IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r0 : Formalism.L2.Theta.ResEta D 1 0 := ⟨rT.1, fun _ _ _ => by simp⟩
  have r1 : Formalism.L2.Theta.ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank :=
    Formalism.L2.Theta.resEta_parity r0 (by show 0 % 2 = (S.rank + S.rank) % 2; omega)
  obtain ⟨ωd, hωd⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp S) T 1 χT hψ h1 hT r1 rT
  refine ⟨ωd, hωd, ?_⟩
  exact GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA
    (GlobalTheory.T.doubledGram_satisfies_xi_relation D S JB ξ hξ) (κ ⊕ κ) (ddr co) (GlobalTheory.T.doubledDarbouxCoords_rational_of_rational D S T JA JB ξ κ co hco) ωd hωd

end GlobalTheory.DblSchr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberDeformationLiftModification
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_isDef_lift_dualNumber : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q) (zw : Sp (DualNumber K) ⟶ M.X) (hw : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zw = z), ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ zw ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ _ z ho Q hz zw hw
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hwU : ⊤ ≤ (zw ≫ M.σ) ⁻¹ᵁ U₀ X Z :=
    le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ _ (by rw [← Category.assoc, hw]; exact hU)
  have hF : ⊤ ≤ (zw ≫ toFlag M) ⁻¹ᵁ flagOpen X := hwU
  have hr : Set.range (zw ≫ toFlag M) ⊆ Set.range X.inc := by
    rintro _ ⟨s, rfl⟩
    exact (opensRange_inc X).ge (hF (Set.mem_univ s))
  obtain ⟨w, hwi⟩ : ∃ w, w ≫ X.inc = zw ≫ toFlag M := ⟨_, IsOpenImmersion.lift_fac X.inc _ hr⟩
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ w = X.pt Q := by
    rw [← cancel_mono X.inc, Category.assoc, hwi, X.pt_inc, ← hz, ← Category.assoc]
    exact congrArg (· ≫ toFlag M) hw

  have hnil : IsNilpotent (RingHom.ker (GlobalTheory.FlagTan.red c K).toRingHom) := ⟨2, by
    rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']⟩
  have hs : w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) := by
    obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* DualNumber K, spMap φ = w ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
      ⟨(Spec.preimage (w ≫ pullback.snd _ _ ≫ pullback.snd _ _)).hom, by
        rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    have h1 : spMap ((GlobalTheory.FlagTan.red c K).toRingHom.comp φ) = spMap (algebraMap c.F K) := by
      show Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom (GlobalTheory.FlagTan.red c K).toRingHom) = _
      rw [Spec.map_comp]
      change spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ spMap φ = _
      rw [hφ, ← Category.assoc, hred, ← Category.assoc, X.pt_snd, frX_snd]
    have h2 : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = algebraMap c.F K :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsSeparable ℚ c.F := inferInstance
    haveI : Algebra.FormallyUnramified ℚ c.F := Algebra.FormallyUnramified.of_isSeparable ℚ c.F
    haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
    haveI : Algebra.FormallyUnramified ℤ c.F := Algebra.FormallyUnramified.comp ℤ ℚ c.F
    have h3 := Algebra.FormallyUnramified.ext' (R := ℤ) (A := c.F) (B := DualNumber K)
      (GlobalTheory.FlagTan.red c K).toRingHom hnil φ.toIntAlgHom (algebraMap c.F (DualNumber K)).toIntAlgHom
      (fun x => by
        show (GlobalTheory.FlagTan.red c K).toRingHom (φ x) =
          (GlobalTheory.FlagTan.red c K).toRingHom (algebraMap c.F (DualNumber K) x)
        exact (RingHom.congr_fun h2 x).trans ((GlobalTheory.FlagTan.red c K).commutes x).symm)
    rw [← hφ]
    exact congrArg spMap (congrArg AlgHom.toRingHom h3)
  obtain ⟨P', hP'⟩ := ((X.points (S := DualNumber K)).1 w).1 hs
  obtain ⟨P'', hP''⟩ := GlobalTheory.FlagMod.exists_frMap (GlobalTheory.FlagTan.red c K) P'
  have e1 : X.pt P'' = X.pt Q := by rw [← X.pt_frMap hP'', hP', hred]
  obtain ⟨t, ht⟩ := ((X.points (S := K)).2 P'' Q).1 e1
  obtain ⟨g, hgl, hgd, hc⟩ := (GlobalTheory.Frames.frBor_iff_frChg P'' Q t).1 ht
  have hdet : ∀ τ, IsUnit ((g τ).map (GlobalTheory.FlagTan.cst c K)).det := fun τ => by
    have h0 : IsUnit (g τ).det := by
      rw [Matrix.det_of_lowerTriangular (g τ) fun i j hij => hgl τ i j hij]
      exact IsUnit.prod_univ_iff.2 fun i => by rw [hgd]; exact Units.isUnit _
    have := h0.map (GlobalTheory.FlagTan.cst c K).toRingHom
    rwa [RingHom.map_det] at this
  obtain ⟨w', hW, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ P' (fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K))
    (Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t none)) hdet
  have hdefQ : IsDef Q w' := by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW hP'').2 ?_
    convert hc using 2 with τ
    · ext i j; simp
    · rfl
  have hB : FrBor (fun i => Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t i)) P' w' :=
    (GlobalTheory.Frames.frBor_iff_frChg P' w' _).2 ⟨fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K),
      fun τ i j hij => by simp [hgl τ i j hij], fun τ i => by simp [hgd], hW⟩
  refine ⟨w', hdefQ, ?_⟩
  rw [← X.ptY_frBor hB, ← X.pt_inc, hP', hwi]

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteDvrEmbedding

theorem exists_injective_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O)
    [Algebra A B] [Algebra.IsIntegral A B] (hφ : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 v hv h_14 h_15 hφ j hj; exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral)
  | exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | (apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral ..)

theorem exists_embedding_padicComplexInt :
    ∀ T : CDVR, T.FinRes → ∃ (p : ℕ) (_ : Fact p.Prime) (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]), ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by
  intro T hT
  haveI : Finite (IsLocalRing.ResidueField T.V) := hT
  obtain ⟨p, hp, _, hfin⟩ := GlobalTheory.exists_padicInt_algebra_finite T.V
  have hinj : Function.Injective (algebraMap ℤ_[p] T.V) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0
      (PadicInt.irreducible_p (p := p))
    rw [map_mul, map_pow, map_natCast] at ha
    exact mul_ne_zero (u.isUnit.map _).ne_zero
      (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) ha
  have hj : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p)) :=
    (algebraMap ℚ_[p] ℂ_[p]).injective.comp Subtype.val_injective
  obtain ⟨kO, hkO⟩ := exists_injective_of_integral _ (PadicComplexInt.integers p) hinj (padicIntHom p) hj
  exact ⟨p, hp, IsFractionRing.lift (K := T.Fr) hkO, kO, fun a => (IsFractionRing.lift_algebraMap hkO a).symm⟩

end GlobalTheory.CompleteDvrEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidueStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_inertia_tateModule_finite_residue : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) → ∃ E : ℕ, 0 < E ∧ ∀ σ ∈ inertia K V, galTate A l σ ^ E = 1 := by
  first | exact @GlobalTheory.InertiaTate.exists_exponent_inertia_galTate | exact GlobalTheory.InertiaTate.exists_exponent_inertia_galTate | (intros; apply GlobalTheory.InertiaTate.exists_exponent_inertia_galTate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fg_subring_descent_group_sections_curve : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  first | exact @GlobalTheory.SpreadCurve.group_sections_curve_descend | exact GlobalTheory.SpreadCurve.group_sections_curve_descend | (intros; apply GlobalTheory.SpreadCurve.group_sections_curve_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisSmulEqValuationSubringOverDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_smul_eq_valuationSubring_over_dvr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω] (V V' : ValuationSubring Ω), IsAbove R K V.toSubring → IsAbove R K V'.toSubring → ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  first | exact @GlobalTheory.ValConj.exists_smul_eq_of_isAbove | exact GlobalTheory.ValConj.exists_smul_eq_of_isAbove | (intros; apply GlobalTheory.ValConj.exists_smul_eq_of_isAbove <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkData
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

noncomputable section

namespace GlobalTheory.Nef

theorem exists_stalk_fac {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X)
    (h : f (IsLocalRing.closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem exists_stalk_map {X Y : Scheme.{0}} (x : X) (g : X ⟶ Y) (y : Y) (hy : g x = y) :
    ∃ φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x, Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ g := by
  subst hy
  exact exists_stalk_fac (g x) (X.fromSpecStalk x ≫ g) (congrArg (fun z => g z) Scheme.fromSpecStalk_closedPoint)

theorem stalk_hom_eq {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} (φ ψ : X.presheaf.stalk x ⟶ R)
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map ψ ≫ X.fromSpecStalk x) : φ = ψ :=
  Spec.map_injective ((cancel_mono (X.fromSpecStalk x)).1 h)

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem unitSec_sqr : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h2 : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id, ← Hom.mul_def, ← h1, _root_.one_mul]
  change η[G].left ≫ (𝟙 G * 𝟙 G : G ⟶ G).left = η[G].left
  rw [← Over.comp_left, h2]

theorem sqr_hom : sqr G ≫ G.hom = G.hom := Over.w _

end

theorem stalkData_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m,
    StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  intro S G _ s
  obtain ⟨π, hπ⟩ := exists_stalk_map (unitSec G s) G.hom s (by
    rw [← Scheme.Hom.comp_apply, sec_hom]; rfl)
  obtain ⟨ε, hε⟩ := exists_stalk_map s (unitSec G) (unitSec G s) rfl
  obtain ⟨m, hm⟩ := exists_stalk_map (unitSec G s) (sqr G) (unitSec G s) (by
    rw [← Scheme.Hom.comp_apply, unitSec_sqr])
  refine ⟨π.hom, ε.hom, m.hom, ⟨hπ, hε, hm⟩, ?_, ?_, ?_⟩
  · have : π ≫ ε = 𝟙 _ := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hε, Category.assoc, sec_hom,
        Category.comp_id, Spec.map_id, Category.id_comp])
    exact congrArg CommRingCat.Hom.hom this
  · have : π ≫ m = π := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hm, Category.assoc, sqr_hom])
    exact congrArg CommRingCat.Hom.hom this
  · have : m ≫ ε = ε := stalk_hom_eq (unitSec G s) _ _ (by
      rw [Spec.map_comp, Category.assoc, hm, ← Category.assoc, hε, Category.assoc, unitSec_sqr])
    exact congrArg CommRingCat.Hom.hom this

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomExtOfGrpPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

theorem exists_hom_ext_of_grpPullback {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
    [Algebra V F] [IsFractionRing V F] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') {t t' : Over (Sp F)} [GrpObj t] [GrpObj t'] {a : t.left ⟶ G.left}
    {a' : t'.left ⟶ G'.left} (ha : IsGrpPullback t G (spMap (algebraMap V F)) a)
    (ha' : IsGrpPullback t' G' (spMap (algebraMap V F)) a') (β : t ⟶ t') [IsMonHom β] :
    ∃ f : G ⟶ G', IsMonHom f ∧ a ≫ f.left = β.left ≫ a' := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso ha (isGrpPullback_pullback G _)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso ha' (isGrpPullback_pullback G' _)
  have hφ₁ : e.hom.left ≫ pullback.fst G.hom (spMap (algebraMap V F)) = a := hφ
  have hφ₂ : e'.hom.left ≫ pullback.fst G'.hom (spMap (algebraMap V F)) = a' := hφ'
  obtain ⟨f, ⟨hf, hfβ⟩, -⟩ := semiAbelian_hom_extends_uniquely_dvr V F G G' hG hG' (e.inv ≫ β ≫ e'.hom)
    inferInstance
  refine ⟨f, hf, ?_⟩
  have A : ((Over.pullback (spMap (algebraMap V F))).map f).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ f.left := pullback.lift_fst _ _ _
  have B : β ≫ e'.hom = e.hom ≫ (Over.pullback (spMap (algebraMap V F))).map f := by
    rw [hfβ]; simp
  rw [← hφ₁, ← hφ₂, Category.assoc, ← A, ← Category.assoc, ← Category.assoc β.left, ← Over.comp_left,
    ← Over.comp_left, B]

theorem pointOver_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [StarRing (𝓞 E)] (T : CDVR) (x₀ : Sp T.Fr ⟶ Xo.X) (k : T.Fr →+* C) (kO kO' : T.V →+* O) (P P' : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (ψ' : P'.A.A.left ⟶ Xo.univ.t.G.left), PointOver P x₀ k kO ψ → PointOver P' x₀ k kO' ψ' → ∃ (α : P.A.A ≅ P'.A.A) (gm : P.G ⟶ P'.G), IsMonHom α.hom ∧ IsMonHom gm ∧ α.hom.left ≫ ψ' = ψ ∧ α.hom.left ≫ P'.gen = P.gen ≫ gm.left ∧ (∀ a, P.oA.act a ≫ α.hom = α.hom ≫ P'.oA.act a) ∧ LBIso P.A.L (P'.A.L.pull α.hom.left) := by
  intro E _ _ _ H Dw l Xo p _ C _ v O _ _ _ T x₀ k kO kO' P P' ψ ψ' h h'
  obtain rfl : kO = kO' := RingHom.ext fun a => P.integers.hom_inj ((h.1 a).trans (h'.1 a).symm)
  obtain ⟨α, hα, hαψ⟩ := grpPullback_iso h.isGrpPullback h'.isGrpPullback
  have hact : ∀ a, P.oA.act a ≫ α.hom = α.hom ≫ P'.oA.act a := fun a =>
    Over.OverMorphism.ext (h'.isGrpPullback.1.hom_ext
      (by rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hαψ, h'.act a, h.act a,
        ← Category.assoc, hαψ])
      ((Over.w _).trans (Over.w _).symm))
  obtain ⟨-, G, t, m₁, m₂, π, φ, hπ, -, hφ, e₂, e₁, hL⟩ := h
  obtain ⟨-, G', t', n₁, n₂, π', φ', hπ', -, hφ', e₂', e₁', hL'⟩ := h'
  obtain ⟨β, hβ, hβφ⟩ := grpPullback_iso m₁.cart n₁.cart
  obtain ⟨f, hf, hfβ⟩ := exists_hom_ext_of_grpPullback G.semi G'.semi m₂.cart n₂.cart β.hom
  have w : (π ≫ f.left) ≫ G'.G.hom = P.G.hom ≫ spMap kO := by rw [Category.assoc, Over.w, hπ.1.w]
  let gm : P.G ⟶ P'.G := Over.homMk (hπ'.1.lift _ _ w) (hπ'.1.lift_snd _ _ w)
  have hgm : gm.left ≫ π' = π ≫ f.left := hπ'.1.lift_fst _ _ w
  have c : α.hom.left ≫ φ' = φ ≫ β.hom.left := n₁.cart.1.hom_ext
    (by rw [Category.assoc, Category.assoc, e₁', hβφ, e₁, hαψ])
    (by rw [Category.assoc, Category.assoc, Over.w, hφ.1.w, hφ'.1.w, Over.w_assoc])
  refine ⟨α, gm, hα, Out.PullGtPf.isMonHom_of_grpPullback hπ hπ' f gm hgm, hαψ, ?_, hact, ?_⟩
  · refine hπ'.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hgm, ← e₂', ← Category.assoc, c, ← Category.assoc, ← e₂,
        Category.assoc, Category.assoc, hfβ]
    · rw [Category.assoc, Category.assoc, Over.w, P.gen_pull.1.w, P'.gen_pull.1.w, Over.w_assoc]
  · refine LBIso.trans P.A.isLB (pull_isLB Xo.univ.t.PP.isLB ψ) (pull_isLB P'.A.isLB _) hL (LBIso.symm ?_)
    exact LBIso.chartPull (Geo.Tor.chartPullPull P'.A.L _ _ rfl)
      (chartPullSame Xo.univ.t.PP.L (fun _ : PUnit => ψ) (fun _ => ψ') (fun _ => 1) _ (fun _ => hαψ.symm)) hL'

end GlobalTheory.CompHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianEvalRingPointNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

namespace GlobalTheory

open GlobalTheory.TopForm in

theorem CanonLB.exists_jacobian_evalPt_ne_zero : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i), ∃ g : Fin D → Γ(Y, K.bundle.U i), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 := by
  intro k _ Y p D _ K i F _ z hz
  by_contra hcon
  push_neg at hcon
  let Sm : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i)) :=
    Submodule.comap (K.coeff i le_rfl) (RingHom.ker (evalPt z _ hz))
  have hsub : Set.range (dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) (D := D)) ⊆ (Sm : Set _) := by
    rintro _ ⟨g, rfl⟩
    exact (RingHom.mem_ker).2 (hcon g)
  have hle : (⊤ : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i))) ≤ Sm := by
    rw [← span_dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) D]
    exact Submodule.span_le.2 hsub
  have hmem : resForm (le_rfl : K.bundle.U i ≤ K.bundle.U i) (K.om i) ∈ Sm := hle Submodule.mem_top
  have h1 : evalPt z _ hz (K.coeff i le_rfl (resForm le_rfl (K.om i))) = 0 :=
    (RingHom.mem_ker).1 hmem
  rw [K.coeff_om, map_one] at h1
  exact one_ne_zero h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransform
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaParseval

theorem exists_lintegral_sq_eq_mul_setLIntegral_theta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  intro F _ _ ψ hψ κ _ μ hμ ν hν 𝓕 h𝓕
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F κ μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F κ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  refine ⟨(c₁ * μ 𝓕₁)⁻¹, fun Φ hΦ => ?_⟩
  have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F ψ hψ κ Φ hΦ
  have hG : @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) =>
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
  rw [hc _ hG (fun γ hγ w => by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F ψ hψ κ Φ γ hγ w])]
  simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F ψ hψ κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
  rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F κ μ hμ 𝓕₁ h𝓕₁ Φ hΦ, ← mul_assoc c₁, ← mul_assoc,
    ENNReal.inv_mul_cancel (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hctop htop), one_mul]

end GlobalTheory.ThetaParseval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupTateLieStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pdiv_group_tate_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate) (tw : G.TorsionTower P.Gt), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) ∧ (∀ (s : G.Tate) (n : ℕ), (e s : P.T).lev n = (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n))) ∧ ∀ n : ℕ, algebraMap O C (muRoot ζ n) = (P.eps.1.lev n : C) := by
  first | exact @GlobalTheory.RaynaudTower.exists_pDivGroup_raynaud_tower | exact GlobalTheory.RaynaudTower.exists_pDivGroup_raynaud_tower | (intros; apply GlobalTheory.RaynaudTower.exists_pDivGroup_raynaud_tower <;> assumption)
end

