import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstOfSqMulTendstoZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve

theorem fibre_over_scheme {R R' : Type} [CommRing R] [CommRing R'] (W : WeierstrassCurve R) (f : R →+* R')
    {A : Over (Sp R)} {A' : Over (Sp R')} [GrpObj A] [GrpObj A'] {ψ : A.left ⟶ scheme W} [IsIso ψ]
    (hψ : ψ ≫ toSpec W = A.hom) (he : eSec A ≫ ψ = zero W) {v : epsR R ⟶ A}
    {h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h)
    {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap f) φ) {v' : epsR R' ⟶ A'} (hv' : IsVecOver f φ v v') :
    ∃ h' : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0],
      IsPullback (φ ≫ ψ) A'.hom (toSpec W) (spMap f) ∧ eSec A' ≫ φ ≫ ψ = spMap f ≫ zero W ∧
      v'.left ≫ φ ≫ ψ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h' := by
  have hρ : (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (Chart.dualMapR f ∘ ![DualNumber.eps, -1, 0]) = ![DualNumber.eps, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [Chart.dualMapR]
    · simp
    · simp
  have h₁ := h.map_comp (Chart.dualMapR f)
  rw [hρ, hP] at h₁
  refine ⟨h₁, ?_, ?_, ?_⟩
  · exact hφ.1.of_iso (Iso.refl _) (asIso ψ) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hψ]) (by simp)
  · rw [← Category.assoc, PolBaseChange.eSec_comm hφ, Category.assoc, he]
  · rw [← Category.assoc, hv', Category.assoc, hv]
    exact (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)

theorem exists_polAV_invariants : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ (∀ (s' : R →+* ℂ) (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∃ L : PeriodPair, (∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) ∧ s' W.c₄ = 12 * L.g₂ ∧ s' W.c₆ = 216 * L.g₃ ∧ s' W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  intro R _ W hΔ
  obtain ⟨P, ψ, v, hg, hiso, hψ, he, ⟨h, hv⟩, hb⟩ := GlobalTheory.WeierstrassCurve.exists_polAV R W hΔ
  refine ⟨P, v, hg, hb, fun R' _ f P' φ v' hP hv' => ?_, fun s P' φ v' u w hP hv' hd => ?_⟩
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ he hv hP.2.1 hv'
    exact OriginTangent.isLieBasis_eps R W R' f P'.A (φ ≫ ψ) v' h' h1 h2 h3
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W s hψ he hv hP.2.1 hv'
    obtain ⟨hw, x, y, t, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
      GlobalTheory.T.exists_weierstrass_coordinates_on_line R W s P'.A (φ ≫ ψ) v' h' h1 h2 h3 P'.L P'.g u w hd
    obtain ⟨L, hL⟩ := GlobalTheory.exists_periodPair_of_lattice_in_line P'.g u.Λ w (hP.1.trans hg) hw u.discrete u.full
    have hset : (L.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL
    have key := GlobalTheory.invariants_eq_of_periodic_solution L (W.map s) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
      (fun l hl => hper l ((hL l).1 hl)) (fun z hz => heq z fun e => hz ((hL z).2 e)) ht ht0 ht1 hty hlim
    simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_Δ] at key
    exact ⟨hw, L, hL, key⟩

end GlobalTheory.WeierstrassCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PolProd

open GlobalTheory.CechPic GlobalTheory.TripleProd

variable {S : Scheme.{0}}

theorem locZero_add {Y B : Scheme.{0}} {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) :
    LocZero π (c + d) := by
  have h := H.sub ((locZero_base π 0).sub H')
  rwa [map_zero, zero_sub, sub_neg_eq_add] at h

theorem rigidified_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 := by
  exact (cls_eq_zero_iff (pull_isLB hL _)).symm

theorem sym_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Sym A L ↔ LocZero A.hom (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
  refine forall_congr' fun _ => exists_congr fun U => and_congr_right fun _ => ?_
  refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).symm.trans ?_
  have e : cls (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]) (LB.isLB_linComb hL _ _) =
      pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
    refine (cls_linComb hL _ _ _).trans ?_
    rw [Fin.sum_univ_two]
    show (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
      (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = _
    rw [one_zsmul, neg_one_zsmul, map_sub, sub_eq_add_neg, pull_comp]
  rw [e]

theorem eSec_comp {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    eSec A ≫ f.left = eSec G := by
  have h : η[A] ≫ f = η[G] := IsMonHom.one_hom f
  exact congrArg (fun z => z.left) h

theorem inv_comp_left {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    (GrpObj.inv : A ⟶ A).left ≫ f.left = f.left ≫ (GrpObj.inv : G ⟶ G).left := by
  have h : (GrpObj.inv : A ⟶ A) ≫ f = f ≫ GrpObj.inv := GrpObj.inv_hom f
  exact congrArg (fun z => z.left) h

theorem exists_prod_polAV : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P P' : Out.PolAV (Sp R)), ∃ (Q : Out.PolAV (Sp R)) (p : Q.A ⟶ P.A) (q : Q.A ⟶ P'.A), IsMonHom p ∧ IsMonHom q ∧ IsIso (lift p q) ∧ Q.g = P.g + P'.g := by
  intro _ R _ _ P P'
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  obtain ⟨M, hM, eM⟩ := cls_surj (pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB))
  have hd := LB.isLB_div hM (pull_isLB P.isLB p.left)
  have last : LBIso (M.div (P.L.pull p.left)) (P'.L.pull q.left) := by
    refine (cls_eq_iff hd (pull_isLB P'.isLB _)).1 ?_
    rw [cls_div hM (pull_isLB P.isLB p.left), eM, cls_pull P.isLB, cls_pull P'.isLB, add_sub_cancel_left]
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := hB.proper
  have hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom := by
    haveI := P.smoothDim
    haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip P'.smoothDim
    rw [add_comm]
    exact inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))
  have hrig : Out.Rigidified (P.A ⊗ P'.A) M := by
    rw [rigidified_iff _ hM, eM, map_add, ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q,
      (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]
  have hsym : Out.Sym (P.A ⊗ P'.A) M := by
    have h₁ := ((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)
    have h₂ := ((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)
    rw [sym_iff _ hM, eM]
    convert locZero_add h₁ h₂ using 1
    rw [map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p,
      inv_comp_left q]
    abel
  have hamp : Out.RelAmple (P.A ⊗ P'.A) M :=
    (relAmple_iff_isAmpleLB_of_isAffine _ hM).2 (IsAmpleLB.box
      ((relAmple_iff_isAmpleLB_of_isAffine _ P.isLB).1 P.ample) ((relAmple_iff_isAmpleLB_of_isAffine _ P'.isLB).1 P'.ample)
      hM (p := p.left) (q := q.left) (f := P.A.hom) (g := P'.A.hom) (IsPullback.of_hasPullback _ _) last.symm)
  refine ⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym, hamp,
    kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q, inferInstance, inferInstance, ?_, rfl⟩
  show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))
  rw [lift_fst_snd]
  infer_instance

end GlobalTheory.PolProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem PAT.exists_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S), ∃ (T' : PAT H S') (_ : SABMap T'.t T.t f), T'.g = T.g := by
  intro E _ _ _ H S S' f T
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f T.t
  obtain ⟨⟨T', ht, hg⟩, -⟩ := GlobalTheory.T.exists_of_cmTriple_pullback E H S S' f T _ m
  exact ⟨T', ht ▸ m, hg⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPureVectorsPeriodsSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem span_pure_periods_eq_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {p q : ℕ} (Z : CMLat hP p q) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v} = ⊤ := by
  set W := Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  obtain ⟨n, hn, h⟩ := Z.span
  have key : ∀ a, Pe a ∈ W := by
    intro a
    obtain ⟨x, hx⟩ := h a
    have h1 : (n : ℂ) • Pe a ∈ W := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hx, map_sum]
      refine W.sum_mem fun j _ => Submodule.subset_span ?_
      have h2 := Z.pure j (x j)
      rcases j with j | j
      · exact ⟨1, ⟨_, by simpa using h2⟩, rfl⟩
      · exact ⟨-1, ⟨_, by simpa using h2⟩, rfl⟩
    exact (W.smul_mem_iff (Nat.cast_ne_zero.2 hn.ne')).1 h1
  have h3 : Submodule.span ℝ (Set.range Pe) ≤ W.restrictScalars ℝ :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact key a)
  rw [hP.2.2.2.1] at h3
  exact eq_top_iff.2 fun v _ => h3 Submodule.mem_top

theorem exists_pure_vectors_periods_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe) (p q : ℕ) (Z : CMLat hP p q), ∃ (ε : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤˣ) (a : ∀ i, PureType.lat hP (((ε i : ℤ) : ℂ) * H.rt0)), ∀ z : Fin g → ℂ, ∃ c : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℂ, z = ∑ i, c i • Pe (a i) := by
  intro E _ _ _ H D g ty Pe hP p q Z
  have h1 := (FibreExp.free_finite_finrank_of_isPeriod hP).2.2
  rw [datum_finrank_int D] at h1
  have hs := span_pure_periods_eq_top hP Z
  have h2 := Submodule.exists_fun_fin_finrank_span_eq ℂ
    {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  rw [hs, finrank_top, Module.finrank_fin_fun] at h2
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by omega
  rw [hg]
  obtain ⟨f, hf, hsp, -⟩ := h2
  choose ε a ha using hf
  refine ⟨ε, a, fun z => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsp ▸ Submodule.mem_top (x := z))
  exact ⟨c, by simp [ha, hc]⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSecGeneric
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.ThetaDegree

def IsPullOf {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (t : LB.Gen (P.L.pull (eSec P.A))) (θ : P.L.Sec) (y : KeyIn R) : Prop :=
  ∃ (ψ : y.P.A.left ⟶ P.A.left) (w : LB.Iso y.P.L (P.L.pull ψ)), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap f) ψ ∧
    PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec y.P.A) (fun _ => eSec P.A) (fun _ => 1) y.rig t (spMap f) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ y.P.A.left) (z : Z) j k, ψ (r z) ∈ P.L.U j → r z ∈ y.P.L.U k →
      gs (r ≫ ψ) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (y.th.f k)

theorem exists_isPullOf {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (hg : 1 ≤ P.g) {t : LB.Gen (P.L.pull (eSec P.A))} (ht : t.IsGen) (θ : P.L.Sec)
    (hθ : ∀ s : Sp R, ∃ z, P.A.hom z = spMap f s ∧ z ∈ Out.nonzeroLocus θ) : ∃ y : KeyIn R, IsPullOf f P t θ y := by
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R) :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he P.L t).IsGen :=
    Out.LBxP.isGen_pullAlong P.L φ (spMap f) (fun _ : PUnit => eSec P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) t ht
  obtain ⟨th', hth'⟩ := sec_pull_down hw P.isLB hL' θ
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis P'.A P'.smoothDim
  refine ⟨⟨P', hg, _, hr, th', fun s => ?_, v, hv⟩, φ, idIso _, rfl, h, hw,
    (maps_iff (idIso _) (fun _ => eSec P'.A) (fun _ => eSec P.A) _ _ t (spMap f) _ (rigPull_le φ (spMap f) he P.L)
      (fun _ => rfl)).1 (fun p => hr p.1 p.2), hth'⟩
  obtain ⟨z, hz, hz'⟩ := hθ s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (θ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem IsPullOf.exists_keyPB {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [CommRing R'] {f : O →+* R}
    {g : R →+* R'} {P : Out.PolAV (Sp O)} {t : LB.Gen (P.L.pull (eSec P.A))} {θ : P.L.Sec} {y : KeyIn R} {x : KeyIn R'}
    (hy : IsPullOf f P t θ y) (hx : IsPullOf (g.comp f) P t θ x) :
    ∃ v' hv', KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ y g := by
  obtain ⟨ψ, w, hg, hc, hw, hr, hs⟩ := hy
  obtain ⟨φ'', w'', hg'', hc'', hw'', hr'', hs''⟩ := hx
  have hsp : spMap (g.comp f) = spMap g ≫ spMap f := (spMap_comp_spMap f g).symm
  obtain ⟨φ, rfl, hw0⟩ : ∃ φ : x.P.A.left ⟶ y.P.A.left, φ ≫ ψ = φ'' ∧ φ ≫ y.P.A.hom = x.P.A.hom ≫ spMap g :=
    ⟨hc.1.lift φ'' (x.P.A.hom ≫ spMap g) (by rw [hc''.1.w, Category.assoc, hsp]), hc.1.lift_fst _ _ _,
      hc.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap g) φ := hc.cancel (hc''.congr hsp rfl) hw0
  have he : eSec x.P.A ≫ φ = spMap g ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' hw hw'' y.P.isLB x.P.isLB
  rw [hsp] at hr''
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR g) ≫ (y.v i).left) ≫ y.P.A.hom = (epsR R').hom ≫ spMap g := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR R' ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR g) ≫ (y.v i).left := fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange g h y.basis hv'
  have hg' : x.P.g = y.P.g := hg''.trans hg.symm
  refine ⟨_, hb hg', φ, he, w', hg', Chart.dualMapR g, h, (isGen_iff _).2 (T.pgen_cancel P.isLB hw hw''),
    (maps_iff w' _ (fun _ => eSec y.P.A) _ x.rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel P.isLB (fun _ => he) hr hr''),
    KeyPow.appLE_eq_of_stalk _ y.th x.th fun z i k hi hk => ?_, fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨j, hj⟩ := exists_chart P.isLB (ψ (φ z))
    have a := hs _ (𝟙 _ ≫ φ) z j i hj hi
    have b := hs'' _ (𝟙 _) z j k hj hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_sec_generic (hT : Out.SecTwistSt) {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (P : Out.PolAV (Sp O)) {X : Scheme.{0}} {φ : X ⟶ P.A.left} {q : X ⟶ Sp K}
    (hp : IsPullback φ q P.A.hom (spMap (algebraMap O K))) : ∃ (θ : P.L.Sec) (z : X), φ z ∈ Out.nonzeroLocus θ := by
  have := P.isAb.smooth
  have := P.isAb.proper
  obtain ⟨s, hs⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨d, hd, θ, hθ⟩ := SecSpread.exists_spread hp P.isLB s
  obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hk' : φ z ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  have hu : IsUnit (gs φ z _ (θ.f (k PUnit.unit))) := by
    rw [hθ _ z hk']
    exact (SecSpread.isUnit_cst hp.w z hd).mul u
  rw [gs_stalkMap φ z _ hk', isUnit_map_iff] at hu
  exact ⟨θ, z, (mem_nonzeroLocus _ _).2 ⟨_, hk', hu⟩⟩

variable {K : Type} [Field K] [NumberField K]

theorem exists_scalar (hT : Out.SecTwistSt) (P : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left)
    (w : LB.Iso x.P.L (P.L.pull φ)) (hg : x.P.g = P.g)
    (hφ : IsGrpPullback x.P.A P.A (spMap (algebraMap (𝓞 K) K)) φ) (hw : w.IsGen) :
    ∃ a : K, a ≠ 0 ∧ {𝔭 | ¬ ∃ M, KeyPow.IsLocalModel x 𝔭 a M}.Finite := by
  have := P.isAb.smooth
  obtain ⟨θ, z₀, hz₀⟩ := exists_sec_generic hT P hφ.1
  obtain ⟨t, ht⟩ := P.rigid
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale P.isLB x.P.isLB ((isGen_iff _).1 hw) (p := x.P.A.hom) (Over.w η[x.P.A])
    (PolBaseChange.eSec_comm hφ) x.rig_gen ht
  obtain ⟨th', hth'⟩ := sec_pull_down g' P.isLB x.P.isLB θ
  have hne : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th' := fun s => by
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz₀
    obtain ⟨k, hk⟩ := exists_chart x.P.isLB z₀
    refine ⟨z₀, Subsingleton.elim (α := PrimeSpectrum K) _ _, (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ z₀ _ (θ.f j)) := by rw [gs_stalkMap φ z₀ _ hj]; exact u.map _
    have e := hth' _ (𝟙 _) z₀ j k hj hk
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  let x' : KeyIn K := ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hne, x.v, x.basis⟩
  have hx' : IsPullOf (algebraMap (𝓞 K) K) P t θ x' := ⟨φ, w', hg, hφ, g', m', hth'⟩
  obtain ⟨a, -, ha, -⟩ := KeyPow.exists_scalar_matrix hT x.P x.th th' x.th_ne x.basis x.basis
  obtain ⟨_, ⟨d, rfl⟩, hd, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_image_of_mem P.A.hom hz₀) (P.A.hom.isOpenMap _ (Out.nonzeroLocus θ).isOpen)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hd (Ideal.zero_mem _)
  refine ⟨a, ?_, (Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd0)).subset fun 𝔭 h𝔭 => ?_⟩
  · rintro rfl
    obtain ⟨z, -, hz⟩ := hne (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  by_contra hn
  refine h𝔭 ?_
  have hv : 𝔭.valuation K (algebraMap (𝓞 K) K d) = 1 := by
    refine (𝔭.valuation_le_one d).antisymm (not_lt.1 fun h => hn ?_)
    exact (𝔭.valuation_lt_one_iff_dvd d).1 h
  let R := (𝔭.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => 𝔭.valuation_le_one r
  have hu : IsUnit (f d) := (Valuation.integer.integers (𝔭.valuation K)).isUnit_iff_valuation_eq_one.2 hv
  obtain ⟨y, hy⟩ := exists_isPullOf f P (hg ▸ x.g_pos) ht θ fun s => by
    have hs : spMap f s ∈ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum (𝓞 K))) := fun h =>
      s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f d ∈ s.asIdeal from h) hu)
    obtain ⟨z, h₁, h₂⟩ := hsub hs
    exact ⟨z, h₂, h₁⟩
  obtain ⟨v', hv', hPB⟩ := hy.exists_keyPB (g := algebraMap R K) (x := x') hx'
  choose M hM using fun i => (x.basis.2 _ (hv'.1 i)).exists
  exact ⟨M, R, _, inferInstance, inferInstance, _,
    inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K), y, th', hne, v', hv', fun r => r.2, ha, hM, hPB⟩

theorem exists_isThetaDeg : Out.SecTwistSt → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K]
    (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth), ∃ δ : ℝ, IsThetaDeg (F.key hg rig hr th hth) δ := by
  intro hT hU K _ _ P F hg rig hr th hth
  classical
  obtain ⟨e, hφ, hL⟩ := F.fib
  obtain ⟨w, hw⟩ := LBIso.symm hL
  let x := F.key hg rig hr th hth
  obtain ⟨oa, od, hloc⟩ := KeyPow.exists_isLocalModel_of_integral hT K P x F.φ w e hφ hw
  obtain ⟨a, ha, hfin⟩ := exists_scalar hT P x F.φ w e hφ hw
  obtain ⟨nth, nη, hn⟩ := KeyPow.exists_archNorms hU x
  have hv : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.valuation K a = WithZero.exp (- -WithZero.log (𝔭.valuation K a)) :=
    fun 𝔭 => by rw [neg_neg, WithZero.exp_log (by simpa using ha)]
  refine ⟨_, fun 𝔭 => if ∃ M, KeyPow.IsLocalModel x 𝔭 a M then -WithZero.log (𝔭.valuation K a) else oa 𝔭, nth,
    fun 𝔭 => ?_, fun σ => ?_, (hfin.union (KeyPow.sum_log_norm_eq_finsum ha _ hv).1).subset fun 𝔭 h => ?_, rfl⟩
  · by_cases h : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · obtain ⟨M, hM⟩ := id h
      exact ⟨a, M, hM, by beta_reduce; rw [if_pos h]; exact hv 𝔭⟩
    · obtain ⟨a', M, hM, h₁, -⟩ := hloc 𝔭
      exact ⟨a', M, hM, by beta_reduce; rw [if_neg h]; exact h₁⟩
  · obtain ⟨x', h₁, h₂⟩ := hn σ
    exact ⟨x', _, h₁, h₂⟩
  · by_cases h' : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · exact Or.inr (by simpa only [Function.mem_support, if_pos h'] using h)
    · exact Or.inl h'

end GlobalTheory.ThetaDegree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.GramStdBasisPosDefAndHq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem gram_stdBasis_posDef_and_hq :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (h : HermFam K (Fin n → K)) (s : K →+* ℂ), (h.gram s (fun i => Pi.single i 1) : Matrix (Fin n) (Fin n) ℂ).PosDef ∧ ∀ c, ReciprocityTheory.MultiplicativeHeights.hq (h.gram s (fun i => Pi.single i 1)) (ReciprocityTheory.MultiplicativeHeights.embVec s c) = (h.form s c c).re := by
  intro K _ _ n h s
  refine ⟨h.posDef s n _ ?_, fun c => ?_⟩
  · have hb := (Pi.basisFun K (Fin n)).linearIndependent
    have he : (⇑(Pi.basisFun K (Fin n)) : Fin n → Fin n → K) = fun i => Pi.single i 1 := by
      funext i; exact Pi.basisFun_apply K (Fin n) i
    rwa [he] at hb
  · have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hx := h.form_expand s c (fun i => Pi.single i 1)
    rw [← hc] at hx
    rw [hx, ReciprocityTheory.MultiplicativeHeights.hq]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ReciprocityTheory.MultiplicativeHeights.embVec, Pi.star_apply,
      Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasType_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap f)) (ρ : R) (p q : ℕ), (Function.Injective f → HasType H t.act ρ p q → HasType H t'.act (f ρ) p q) ∧ ((∀ (k : Type) [Field k] (β : R →+* k), Function.Injective β → ∃ β' : R' →+* k, β'.comp f = β ∧ Function.Injective β') → HasType H t'.act (f ρ) p q → HasType H t.act ρ p q) := by
  intro E _ _ _ H R R' _ _ f t t' m ρ p q
  have key : ∀ (k : Type) [Field k] (β' : R' →+* k) (τ : 𝓞 E →+* k) (n : ℕ),
      LieMult t'.act (spMap β') τ n ↔ LieMult t.act (spMap (β'.comp f)) τ n := fun k _ β' τ n => by
    have e : spMap β' ≫ spMap f = spMap (β'.comp f) := (Spec.map_comp _ _).symm
    rw [← e]
    exact LiePull.lieMult_pull _ _ _ t.G t'.G (spMap f) m.cm.F t.act t'.act m.cart m.act k _ τ n
  refine ⟨fun hf h k _ _ β' hβ' τ => ?_, fun hext h k _ _ β hβ τ => ?_⟩
  · rw [key, key]
    exact h k (β'.comp f) (hβ'.comp hf) τ
  · obtain ⟨β', rfl, hβ'⟩ := hext k β hβ
    rw [← key, ← key]
    exact h k β' hβ' τ

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.integers_of_cm_field_conj_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsDedekindDomain (OK H) ∧ (∀ a : OK H, ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H) ∧ (∃ br : OK H ≃+* OK H, (∀ a, ((br a : OK H) : 𝓞 E) = H.bar a) ∧ wK H + br (wK H) = 1 ∧ ∀ a, br (br a) = a) ∧ wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H ∧ 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E ∧
  ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → Module.Finite (OK H) M ∧ Module.Projective (OK H) M ∧ Module.finrank (OK H) M = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) M := by
  first | exact @GlobalTheory.CM.OK_isDedekindDomain_and_projective | exact GlobalTheory.CM.OK_isDedekindDomain_and_projective | (intros; apply GlobalTheory.CM.OK_isDedekindDomain_and_projective <;> assumption)
end

