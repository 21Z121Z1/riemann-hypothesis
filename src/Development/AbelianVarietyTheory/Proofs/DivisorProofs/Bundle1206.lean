import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueTopFormAlongPrimeDivisorAdjunction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Residue

open KaehlerDifferential IsLocalRing Module

theorem exists_basis_D_cons (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra k V] [Algebra.EssFiniteType k V] (n : ℕ) {t : V}
    (w : Fin n → V) (ht : Irreducible t) (hb₀ : Nonempty (Module.Basis (Fin (n + 1)) V Ω[V⁄k]))
    (hw : ∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (algebraMap k V) w P)) :
    ∃ b : Module.Basis (Fin (n + 1)) V Ω[V⁄k], ∀ i, b i = D k V ((Fin.cons t w : Fin (n + 1) → V) i) := by
  obtain ⟨b₀⟩ := hb₀
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)
  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ (algebraMap k V) w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP
  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg
    simp only [map_add, map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
      Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  exact Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)

theorem residue_dForm : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → ∀ (t f : S.ring) (v w : Fin n → S.ring) (H : L),
  Irreducible t → Irreducible f → TrBasis cK (fun i => ψ (v i)) →
  TrBasis cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
    H • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  ∃ h : S.ring, (h : L) * f = H * t ∧ dForm cK (fun i => ψ (w i)) = ψ h • dForm cK (fun i => ψ (v i)) := by
  intro L K _ _ cL cK n S ψ hψ hc t f v w H ht hf hvK hvL hH
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  letI : Algebra S.ring K := ψ.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : IsScalarTower ℂ S.ring K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hψt : ψ t = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact ht.not_isUnit
  have hb₀ : Nonempty (Module.Basis (Fin (n + 1)) S.ring Ω[S.ring⁄ℂ]) := by
    obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ ht
    have h1 := trdeg_eq_of_basis_kaehler ℂ L b
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hvL
    rw [h1, Cardinal.mk_fin] at h2
    have h3 : n + 1 = m + 1 := by exact_mod_cast h2
    obtain rfl : n = m := by omega
    exact ⟨b⟩
  have hvu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P) := by
    intro P hP
    by_contra hu
    have hm : MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P ∈ RingHom.ker ψ := by
      rw [hker]
      exact hu
    rw [RingHom.mem_ker, MvPolynomial.hom_eval₂, hcomp] at hm
    have hind : AlgebraicIndependent ℂ (fun i => ψ (v i)) := hvK.1
    exact hP ((algebraicIndependent_iff.1 hind) P hm)
  obtain ⟨b, hb⟩ := exists_basis_D_cons ℂ S.ring n v ht hb₀ hvu

  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ ht hf
  set z : Fin (n + 1) → S.ring := Fin.cons t v with hz
  have hω : IsFreeGen S.ring (dForm S.const z) := isFreeGen_dForm z b hb
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) S.ring :=
    Matrix.of fun i j => b.repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i)) j
  have hM : dForm S.const (Fin.cons f w : Fin (n + 1) → S.ring) = M.det • dForm S.const z := by
    refine dForm_eq_det_smul _ _ M fun i => ?_
    change D ℂ S.ring _ = ∑ j, M i j • D ℂ S.ring (z j)
    conv_lhs => rw [← b.sum_repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i))]
    simp only [hb, M, Matrix.of_apply, hz]
  have hcons : ∀ (a : S.ring) (g : Fin n → S.ring),
      (fun i => S.ring.subtype ((Fin.cons a g : Fin (n + 1) → S.ring) i)) =
        (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have htoRat : ∀ (a : S.ring) (g : Fin n → S.ring),
      S.toRat (n + 1) (dForm S.const (Fin.cons a g : Fin (n + 1) → S.ring)) =
        dForm cL (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    exact (formMap_dForm (D := n + 1) S.ring.subtype rfl _).trans (congrArg _ (hcons a g))
  have hML : dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
      (M.det : L) • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) := by
    have := congrArg (S.toRat (n + 1)) hM
    rw [map_smulₛₗ, hz, htoRat, htoRat] at this
    exact this
  have hHM : H = (M.det : L) := by
    have hne := S.toRat_ne_zero hω
    rw [hz, htoRat] at hne
    exact smul_left_injective L hne (hH.symm.trans hML)

  have hmain : M.det * ↑u⁻¹ * f = M.det * t := by
    rw [← hu, mul_comm t, ← mul_assoc, mul_assoc M.det, Units.inv_mul, mul_one]
  refine ⟨M.det * ↑u⁻¹, ?_, ?_⟩
  · rw [hHM]
    exact_mod_cast congrArg Subtype.val hmain
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => ψ (M i.succ j.succ)
  have hN : dForm cK (fun i => ψ (w i)) = N.det • dForm cK (fun i => ψ (v i)) := by
    refine dForm_eq_det_smul _ _ N fun i => ?_
    change D ℂ K (ψ (w i)) = ∑ j, N i j • D ℂ K (ψ (v j))
    have := congrArg (KaehlerDifferential.map ℂ ℂ S.ring K) (b.sum_repr (D ℂ S.ring (w i)))
    rw [map_sum, KaehlerDifferential.map_D, Fin.sum_univ_succ, RingHom.algebraMap_toAlgebra] at this
    rw [← this]
    simp only [map_smul, hb, KaehlerDifferential.map_D, hz, Fin.cons_zero, Fin.cons_succ,
      RingHom.algebraMap_toAlgebra, hψt, map_zero, smul_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K]
    simp [N, M, RingHom.algebraMap_toAlgebra]
  have hDt : D ℂ S.ring t = b 0 := by rw [hb]; rfl
  have hrow : ∀ j, ψ (M 0 j) = ψ (u * Finsupp.single (0 : Fin (n + 1)) (1 : S.ring) j) := by
    intro j
    simp only [M, Matrix.of_apply, Fin.cons_zero]
    rw [← hu, Derivation.leibniz, hDt, map_add, map_smul, map_smul, b.repr_self]
    rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, hψt, zero_mul, zero_add]
  have hsub : (ψ.mapMatrix M).submatrix Fin.succ Fin.succ = N := Matrix.ext fun _ _ => rfl
  have h0 : ∀ j : Fin n, ψ.mapMatrix M 0 j.succ = 0 := fun j => by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp [Finsupp.single_apply, (Fin.succ_ne_zero j).symm]
  have h00 : ψ.mapMatrix M 0 0 = ψ u := by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp
  have hdet : ψ M.det = ψ u * N.det := by
    rw [RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove_zero, hsub]
    simp only [h0, h00, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
      one_mul]
  rw [hN, map_mul, hdet, mul_comm (ψ u), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

end GlobalTheory.Residue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

open GlobalTheory.ExtUnique

theorem ringAct_extends_semiAbelian_dvr : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G ⟶ G), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act a).left ≫ φ = φ ≫ (act' a).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hG hφ O _ act hh h1 hmul hadd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing W L
  have hq : QuasiCompact (spMap (algebraMap W L)) := ‹_›
  have hd : IsSchemeTheoreticallyDominant (spMap (algebraMap W L)) := ‹_›
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap (algebraMap W L))) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G (spMap (algebraMap W L)))
  have ext : ∀ x : O, ∃ F : G ⟶ G, (act x).left ≫ φ = φ ≫ F.left := by
    intro x
    have := hh x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG
      (a.hom ≫ act x ≫ b.hom) inferInstance
    refine ⟨F, ?_⟩
    have h₁ := pullback_map_left_fst (spMap (algebraMap W L)) F
    rw [hF, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi a.hom.left).1 h₁
  choose f hf using ext
  refine ⟨f, ⟨fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩, hf⟩
  · have := hh x
    exact isMonHom_of_isGrpPullback hφ hφ (act x) (f x) (hf x)
  · refine over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, h1, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, hmul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine over_hom_ext_of_isPullback hφ.1 ?_
    let φ₀ : Over.mk (A.hom ≫ spMap (algebraMap W L)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 A (act x) (act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, hadd, ← h]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfLevelOnObjects
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRowsObj

open GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

variable {D : D7}

theorem not_isConjPl (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {PP PP' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : P.Div k PP) (h' : P.Div k' PP') : ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro hc
  obtain ⟨l, -, hl⟩ := Formalism.L2.Pj.levelPb_exists D P.pb P.pb_over
  have hle : ∀ {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.E)}, P.Div k Q → l.Mb ≤ Q.asIdeal := fun {k Q} hQ => by
    rw [hl]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    have e : Q.under (𝓞 D.host.K) = P.pb k := hQ
    rw [Ideal.map_le_iff_le_comap, ← e]
    exact le_rfl
  refine PP'.isPrime.ne_top (top_le_iff.1 (l.coprime.ge.trans (sup_le (hle h') ?_)))
  rw [Ideal.map_le_iff_le_comap]
  intro c hc0
  obtain ⟨c', h1, h2⟩ := hc c (hle h hc0)
  have e : (Formalism.L2.Pj.hostOfRecord D).bar c = c' :=
    RingOfIntegers.ext (((Formalism.L2.Pj.hostOfRecord D).bar_eq c).trans h2.symm)
  show (Formalism.L2.Pj.hostOfRecord D).bar c ∈ PP'.asIdeal
  rwa [e]

theorem liftsExist {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) : LiftsExist (Yc D 0) (L.βY 0) (L.dat0 L.triv) := by
  obtain ⟨c, hc⟩ := hL.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  obtain ⟨k', hk'⟩ := (hL.Pg PP').1 (h'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl _ hk hk'

section Mult

variable {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem hasType_flag1 {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) :
    HasType V β (flag1L L) F := by
  intro κ hκ h
  have hl := GlobalTheory.FlagAction.isLift_one_of_mem hκ
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hl.2.2]; exact P.H.one_mem
  rw [hF κ ⟨hl.1, hl.2.1, hp⟩ h, GlobalTheory.FlagAction.levChi_flag1]
  congr 1
  unfold levChi
  rw [levFn_withP, extendOne_of_mem _ hp, show (⟨_, hp⟩ : P.H) = 1 from Subtype.ext hl.2.2, map_one, one_mul]

theorem mem_mult_withP_iff (hl : LiftsExist V β L) {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (P : LevelP L.Pg L.r ℂ) (U : MMap M) :
    U ∈ Mult θ M (levS V β (withP L P)) (levChi V β (withP L P)) ↔
      U ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) ∧
        ∀ p : P.H, postOn M (actL V β L p.1) U = ((P.chi p : ℂˣ) : ℂ) • U := by
  rw [GlobalTheory.MultMem.mem_mult_iff, GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · intro h
    have hT : ∀ v, HasType V β (withP L P) (U v) := fun v κ hκ y => h.lev v κ hκ y
    refine ⟨⟨h.aut, h.cusp, fun v κ hκ y => hasType_flag1 (hT v) κ hκ y, h.equiv, h.cont⟩, fun p => ?_⟩
    ext v y
    exact congrFun (GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (hT v) p (hl _)) y
  · rintro ⟨h, hP⟩
    refine ⟨h.aut, h.cusp, fun v κ hκ y => ?_, h.equiv, h.cont⟩
    exact IsPLevel.hasType (V := V) (β := β) (L := L) (P := P)
      ⟨fun κ hκ y => h.lev v κ hκ y, fun p => congrArg (fun W : MMap M => W v) (hP p)⟩ κ hκ y

theorem gaL_actL (hl : LiftsExist V β L) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) {c : G → ℂ}
    (hc : ∀ g a, c (g * a * g⁻¹) = c a) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) (g : G) :
    gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F) := by
  have hm : ∀ a b : G, actL V β L (eG a) (actL V β L (eG b) F) = actL V β L (eG (a * b)) F := fun a b => by
    rw [map_mul]
    exact (GlobalTheory.FlagAction.act_mul hF (hl _) (hl _)).symm
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hm]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun a => ?_).symm
  show _ = c (g * a * g⁻¹) • actL V β L (eG (g * a * g⁻¹ * g)) F
  rw [hc, inv_mul_cancel_right]

end Mult

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eC_conj (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (σ : D.what₂.LL →+* ℂ) (g a : G) :
    RealDat.eC (A := A) σ (g * a * g⁻¹) = RealDat.eC (A := A) σ a := by
  have h := congrArg (fun x : MonoidAlgebra D.what₂.LL G => x.coeff (g * a)) (idemOf_central A.X hX (MonoidAlgebra.single g 1))
  simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
    inv_mul_cancel_left] at h
  unfold RealDat.eC
  rw [h]

def rowAct (R : RealDat D A Ks) (g : G) : MMap (R.MY 0) →ₗ[ℂ] MMap (R.MY 0) :=
  postOn _ (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g))

variable {R : RealDat D A Ks}

theorem hasType_of_mem {U : MMap (R.MY 0)} (hU : U ∈ R.EEat R.triv) (v : (R.MY 0).Vec) :
    HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) (U v) :=
  fun κ hκ y => ((GlobalTheory.MultMem.mem_mult_iff ..).1 hU.1).lev v κ hκ y

theorem rowAct_mem (hL : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    (g : G) {U : MMap (R.MY 0)} (hU : U ∈ R.EEat R.triv) : rowAct R g U ∈ R.EEat R.triv := by
  have h2 := ((mem_goodPart _ _ _ _ _ _).1 hU).2
  refine (mem_goodPart _ _ _ _ _ _).2 ⟨?_, fun v => ?_⟩
  · exact GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MY 0) hθ (R.βY 0) (R.dat0 R.triv) (R.eG g) U hU.1 _ fun _ => rfl
  · refine (gaL_actL (liftsExist hL) R.eG (eC_conj hX _) (hasType_of_mem hU v) g).trans ?_
    exact congrArg (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) (h2 v)

def rowRep (hL : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    : Representation ℂ G (R.EEat R.triv) where
  toFun g := (rowAct R g).restrict fun _ hU => rowAct_mem hL hθ hX g hU
  map_one' := by
    refine LinearMap.ext fun U => Subtype.ext (MultilinearMap.ext fun v => ?_)
    show actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG 1) (U.1 v) = U.1 v
    rw [map_one]
    exact GlobalTheory.FlagAction.act_one (hasType_of_mem U.2 v)
  map_mul' g g' := by
    refine LinearMap.ext fun U => Subtype.ext (MultilinearMap.ext fun v => ?_)
    show actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (g * g')) (U.1 v) =
      actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g') (U.1 v))
    rw [map_mul]
    exact GlobalTheory.FlagAction.act_mul (hasType_of_mem U.2 v) (liftsExist hL _) (liftsExist hL _)

def withModel (R : RealDat D A Ks) (M : HMod (MMap (R.MY 0))) (ρ : Representation ℂ G M.H) (Θ : ∀ t, (R.HX t).H →ₗ[ℂ] M.H) :
    RealDat D A Ks :=
  { R with HE := M, gE := ρ, Th := Θ }

def modelEquiv {M : HMod (MMap (R.MY 0))} (hM : M.Is (R.EEat R.triv) (ipM (R.MY 0) R.ν0 R.fd0)) : M.H ≃ₗ[ℂ] R.EEat R.triv :=
  (LinearEquiv.ofInjective M.e hM.1).trans (LinearEquiv.ofEq _ _ hM.2.1)

def modelRep (hL : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    {M : HMod (MMap (R.MY 0))} (hM : M.Is (R.EEat R.triv) (ipM (R.MY 0) R.ν0 R.fd0)) :
    Representation ℂ G M.H :=
  (modelEquiv hM).symm.conjRingEquiv.toMonoidHom.comp (rowRep hL hθ hX)

theorem exists_model (hθ : IsInfFam R.θ) (hν : R.models_ν0)
    (hfin : FiniteDimensional ℂ (Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv))))
    (hS : SchurMult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.ν0 R.fd0) :
    ∃ M : HMod (MMap (R.MY 0)), M.Is (R.EEat R.triv) (ipM (R.MY 0) R.ν0 R.fd0) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D R.θ _ _ (R.MY 0) _ _ R.ν0 R.fd0 hθ hν.1.1 hν.2 hS
    (GlobalTheory.GardingVec.sm_ne_bot D _ _ _)
  exact GlobalTheory.HilbertModel.exists_hmod _ _ _ (Submodule.finiteDimensional_of_le (goodPart_le _ _ _ _ _))
    (fun x hx y hy z hz => h1 x hx.1 y hy.1 z hz.1) fun x hx => h2 x hx.1

end GlobalTheory.LevelRowsObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOrthogonalKernel
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem section1_mem_orthogonal_ker : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N →
    ∀ (B : N →ₗ⋆[ℂ] N →ₗ[ℂ] ℂ) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N),
    Ψ ∈ ((filt M.act N k).comap (phiN M.act N (k + 1))).orthogonalBilin (formT (k + 1) B) →
    ∀ i g, section1 Ψ i g ∈ (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) := by
  intro R S M N hN B k Ψ hΨ i g
  classical
  rw [Submodule.mem_orthogonalBilin_iff]
  intro x hx
  let Φ : (Fin (k + 1) → NC R S) → N := fun g' =>
    if ∀ j, j ≠ i → g' j = g j then x (fun _ => g' i) else 0
  have hΦ : Φ ∈ (filt M.act N k).comap (phiN M.act N (k + 1)) := by
    rw [Submodule.mem_comap]
    apply GlobalTheory.T.filtration_step_from_section_kernel R S M N hN k i Φ
    intro g''
    by_cases h : ∀ j, j ≠ i → g'' j = g j
    · have e : section1 Φ i g'' = x := by
        funext h'
        simp only [section1, Φ]
        rw [if_pos (fun j hj => by rw [Function.update_of_ne hj]; exact h j hj)]
        simp only [Function.update_self]
        congr 1
        funext j
        rw [Subsingleton.elim j 0]
      rw [e]
      exact hx
    · have e : section1 Φ i g'' = 0 := by
        funext h'
        simp only [section1, Φ]
        rw [if_neg]
        · rfl
        · intro hc
          apply h
          intro j hj
          have := hc j hj
          rwa [Function.update_of_ne hj] at this
      rw [e, map_zero]
  have h0 : formT (k + 1) B Φ Ψ = 0 := (Submodule.mem_orthogonalBilin_iff.1 hΨ) Φ hΦ
  have key : formT (k + 1) B Φ Ψ = ∑ y, B (x (fun _ => y)) (Ψ (Function.update g i y)) := by
    rw [formT_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Function.update g i)))]
    · rw [Finset.sum_image (fun a _ b _ hab => Function.update_injective g i hab)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Φ]
      rw [if_pos (fun j hj => Function.update_of_ne hj _ _)]
      simp only [Function.update_self]
    · intro g' _ hg'
      simp only [Φ]
      rw [if_neg, map_zero, LinearMap.zero_apply]
      intro hc
      apply hg'
      rw [Finset.mem_image]
      refine ⟨g' i, Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, hc j hj]
  show formT 1 B x (section1 Ψ i g) = 0
  rw [key] at h0
  rw [formT_apply]
  refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ fun h => ?_).trans h0
  simp only [section1, Equiv.funUnique_apply]
  congr 2
  congr 1
  funext j
  rw [Subsingleton.elim j default]

end GlobalTheory.SteepMult

end
end

