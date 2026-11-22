import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValuesOfSectionsCompleteLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3461
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValuesOfSectionsCompleteLocalRingStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∃ (e : Ωˣ) (p0 p0' : Ω), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) p0 p0' k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  first | exact @GlobalTheory.HeatValues.heat_values_at_point | exact GlobalTheory.HeatValues.heat_values_at_point | (intros; apply GlobalTheory.HeatValues.heat_values_at_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeBundleTrivialGeometricFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeckeFibre

theorem transl_triv {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (M : LB A.left) (hM : M.IsLB) (hR : Out.Rigidified A M) (K : Type) [Field K] [IsAlgClosed K]
    (y : Sp K ⟶ S) (n : ℕ) (hn : (n : K) ≠ 0) (x : Over.mk y ⟶ A) (hx : x ^ n = 1)
    (h : ∀ z : Over.mk y ⟶ A, z ^ n = 1 → Out.WeilIs A M (n : ℤ) x z 1) :
    ∃ t : (Out.translDiff A M x).Gen, t.IsGen := by
  obtain ⟨L, hL, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ A hA M hM hR
    (GlobalTheory.WeilIntegral.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hM)
  subst hL
  exact GlobalTheory.OrthKer.mem_kernel_of_cubWeil_orthogonal K S y A hA L c n hn x hx
    (fun z hz => (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA hx hz 1).2 (h z hz))

theorem pic_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c (IsLocalRing.closedPoint K)
  have h := GlobalTheory.AbDual.pull_eq_zero_of_mem V (𝟙 _) (fun z => by
    have : z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc
  rwa [GlobalTheory.CechPic.pull_id] at h

theorem rigidified_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) :
    Out.Rigidified A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 rig₁
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp]
  have e : eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
      rw [MonObj.comp_one, CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    simp only [eSec, ← Over.comp_left, comp_lift, Category.comp_id, h1]
  rw [e, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _), h0, map_zero]

end GlobalTheory.HeckeFibre

namespace GlobalTheory.HeckeFibre

theorem fibre_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  intro p _ D R _ b g c k N hc hk hN3 hNp hEF hsurj hdvd S s o h hh K _ _ y
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal D K _ _ _ I g c k N hc hk (by omega) hNp hEF hsurj hdvd x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := transl_triv o.A o.ab _ (pull_isLB o.isLB _) (rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.T.biextension_trivial_of_translate_difference_trivial o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y) (pic_field_eq_zero K)
    (o.eta (N • g x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.HeckeFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointnessIsoExtendsDescendedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ExtAdj

section Gen
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_normalized {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B)
    (s : LB.Gen (LB.LinComb L ψ ε)) (hs : s.IsGen) :
    ∃ s₂ : LB.Gen (LB.LinComb L (Sum.elim ψ (fun k => p ≫ e ≫ ψ k)) (Sum.elim ε (fun k => -ε k))),
      s₂.IsGen ∧ ∀ y J, Good L y J → val s₂ e y J = 1 := by
  refine ⟨LB.mulGen L _ _ _ _ s (LB.pullGen L _ _ (LB.invGen L _ _ (LB.pullGen L ψ ε s e)) p),
    DVR.mulGen_isGen _ _ _ _ _ _ _ hs (DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hs e)) p), fun y J hJ => ?_⟩
  rw [val_mul hJ, val_pull hJ, val_inv, val_pull hJ, he, Category.id_comp, mul_inv_cancel]

theorem formEq_sec {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B) :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (B ⟶ X)) PEmpty.elim
      (fun k => e ≫ Sum.elim ψ (fun k => p ≫ e ≫ ψ k) k) (Sum.elim ε (fun k => -ε k)) := by
  intro U _ h
  rw [Fintype.prod_empty, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Category.assoc, he, Category.id_comp, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel]
end Gen

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S}

def cφ (x : Fin 2 → (T ⟶ G)) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ G.left) := fun I => (psum G x I.down).left

def cε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem cls_diff {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (h : (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))).IsLB) :
    CechPic.cls _ h = CechPic.cls (LB.LinComb L (cφ x₁) cε) (LB.isLB_linComb hL _ _) -
      CechPic.cls (LB.LinComb L (cφ x₂) cε) (LB.isLB_linComb hL _ _) := by
  rw [CechPic.cls_linComb hL, CechPic.cls_linComb hL, CechPic.cls_linComb hL, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem lbIso_of_gen {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I)))) (ht : t.IsGen) :
    LBIso (cubeLB G x₁ L) (cubeLB G x₂ L) := by
  have z := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_diff hL x₁ x₂, sub_eq_zero] at z
  exact (CechPic.cls_eq_iff _ _).1 z

theorem gen_of_lbIso {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (H : LBIso (cubeLB G x₁ L) (cubeLB G x₂ L)) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))), t.IsGen := by
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [cls_diff hL x₁ x₂, sub_eq_zero]
  exact (CechPic.cls_eq_iff (LB.isLB_linComb hL (cφ x₁) cε) (LB.isLB_linComb hL (cφ x₂) cε)).2 H

end Cube

section Origin
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem eSec_cφ (x : Fin 2 → (G2 G ⟶ G)) (hx : ∀ i, η[G2 G] ≫ x i = 1) (I : ULift.{0} (Finset (Fin 2))) :
    eSec (G2 G) ≫ cφ x I = eSec G := by
  have h1 : η[G2 G] ≫ psum G x I.down = 1 := by
    have a := psum_hom (preHom (G := G) η[G2 G]) x I.down
    have b := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ => 1) I.down
    simp only [MonoidHom.one_apply] at b
    exact a.trans ((congrArg (fun z => psum G z I.down) (funext hx)).trans b.symm)
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  refine h2.trans ?_
  simp [Hom.one_def, eSec]

theorem eSec_x2 (i : Fin 2) : η[G2 G] ≫ x2 G i = η[G] := by
  fin_cases i <;> simp [x2]

theorem one_cube₁ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G ≫ f, snd G G] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]

theorem one_cube₂ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G, snd G G ≫ f] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]
end Origin

section Push
variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {e : A.left ⟶ G.left}

abbrev jTwo (he : IsGrpPullback A G j e) : (G2 A).left ⟶ (G2 G).left :=
  (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A))).left

theorem doubleProductMapOfGrpPullback_comp_doubleCoordinate (he : IsGrpPullback A G j e) (i : Fin 2) : jTwo he ≫ (x2 G i).left = (x2 A i).left ≫ e := by
  fin_cases i
  · exact congrArg (fun z => z.left) (lift_fst (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
  · exact congrArg (fun z => z.left) (lift_snd (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))

theorem eSec_jTwo (he : IsGrpPullback A G j e) : eSec (G2 A) ≫ jTwo he = j ≫ eSec (G2 G) := by
  refine GlobalTheory.Mum.PowCart.square_over_hom_ext _ fun i => ?_
  have a : eSec (G2 A) ≫ (x2 A i).left = eSec A := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := A) i)
  have b : eSec (G2 G) ≫ (x2 G i).left = eSec G := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := G) i)
  rw [Category.assoc, doubleProductMapOfGrpPullback_comp_doubleCoordinate, ← Category.assoc, a, Category.assoc, b]
  exact (cubeMapOf he).e_comm

theorem cφ_push (he : IsGrpPullback A G j e) (x' : Fin 2 → (G2 A ⟶ A)) (x : Fin 2 → (G2 G ⟶ G))
    (hx : ∀ i, (x' i).left ≫ e = jTwo he ≫ (x i).left) (I : ULift.{0} (Finset (Fin 2))) :
    cφ x' I ≫ e = jTwo he ≫ cφ x I :=
  psum_push he x' x (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
    (fun i => Over.OverMorphism.ext (by rw [Over.comp_left]; exact hx i)) I.down
end Push

section Drop
variable {X Y B : Scheme.{0}} {K0 : Type} [Fintype K0]

theorem formEq_drop {ψ : K0 ⊕ K0 → (Y ⟶ X)} {ε₀ : K0 → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (z : B ⟶ X)
    (hz : ∀ k, e ≫ ψ k = z) :
    FormEq (Sum.elim ψ (fun k => p ≫ e ≫ ψ k))
      (Sum.elim (Sum.elim ε₀ (fun k => -ε₀ k)) (fun k => -(Sum.elim ε₀ (fun k => -ε₀ k)) k))
      ψ (Sum.elim ε₀ (fun k => -ε₀ k)) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hz, zpow_neg, neg_neg, inv_inv,
    Finset.prod_inv_distrib]
  group
end Drop

theorem adj_extends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hsa he _ act hact PP cub cm hF _ hpc a
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU
  have := hsa.smooth
  have := hsa.geomConnected
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  haveI : IsDominant j := ⟨hdense⟩
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  obtain ⟨w, hw, -, -⟩ := hpc
  have hw' := (isGen_iff w).1 hw
  haveI := act.hom a
  haveI := act.hom (H.bar a)
  haveI := tF.act.hom a
  haveI := tF.act.hom (H.bar a)
  let x₁ : Fin 2 → (G2 G ⟶ G) := ![fst G G ≫ act.act a, snd G G]
  let x₂ : Fin 2 → (G2 G ⟶ G) := ![fst G G, snd G G ≫ act.act (H.bar a)]
  let y₁ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G ≫ tF.act.act a, snd tF.G tF.G]
  let y₂ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G, snd tF.G tF.G ≫ tF.act.act (H.bar a)]
  let ψ := Sum.elim (cφ x₁) (cφ x₂)
  let ψ' := Sum.elim (cφ y₁) (cφ y₂)
  let ε₁ : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim cε (fun I => -cε I)
  obtain ⟨s, hs⟩ := gen_of_lbIso tF.PP.isLB y₁ y₂ (tF.adj a)
  obtain ⟨s₂, hs₂, h1⟩ := exists_normalized (G2 tF.G).hom (eSec (G2 tF.G)) (CubeExtension.eSec_comp _) s hs
  have hsm := CubeExtension.smooth_tensor G G
  have hgc := CubeExtension.geometricallyConnected_tensor G G
  have hpb : IsPullback (jTwo he) (G2 tF.G).hom (G2 G).hom j := GlobalTheory.Mum.PowCart.isPullback_two he.1
  have f0 : jTwo he ≫ (fst G G).left = (fst tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 0
  have f1 : jTwo he ≫ (snd G G).left = (snd tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 1
  have hψ : ∀ k, ψ' k ≫ e = jTwo he ≫ ψ k := by
    rintro (I | I)
    · refine cφ_push he y₁ x₁ (fun i => ?_) I
      fin_cases i
      · show (fst tF.G tF.G ≫ tF.act.act a).left ≫ e = jTwo he ≫ (fst G G ≫ act.act a).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact a, ← Category.assoc, ← f0, Category.assoc]
      · exact f1.symm
    · refine cφ_push he y₂ x₂ (fun i => ?_) I
      fin_cases i
      · exact f0.symm
      · show (snd tF.G tF.G ≫ tF.act.act (H.bar a)).left ≫ e = jTwo he ≫ (snd G G ≫ act.act (H.bar a)).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact (H.bar a), ← Category.assoc, ← f1, Category.assoc]
  have hφ : ∀ k, Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k) k ≫ cm.F =
      jTwo he ≫ Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k) k := by
    rw [hF]
    rintro (k | k)
    · exact hψ k
    · simp only [Sum.elim_inr, Category.assoc]
      rw [hψ k, ← Category.assoc (eSec (G2 tF.G)), eSec_jTwo he, Category.assoc, ← Category.assoc (G2 tF.G).hom,
        ← hpb.w, Category.assoc]
  obtain ⟨c', hc', -⟩ := DenseCubeExt.exists_extension hS j (G2 G).hom (eSec (G2 G)) (jTwo he) (G2 tF.G).hom
    (eSec (G2 tF.G)) hsm hgc (CubeExtension.eSec_comp _) hpb (eSec_jTwo he) PP.isLB tF.PP.isLB hw'
    (Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k)) (Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k))
    (Sum.elim ε₁ (fun k => -ε₁ k)) hφ (formEq_sec _ _ (CubeExtension.eSec_comp _))
    (formEq_sec _ _ (CubeExtension.eSec_comp _)) s₂ hs₂ h1
  have hz : ∀ k, eSec (G2 G) ≫ ψ k = eSec G := by
    rintro (I | I)
    · exact eSec_cφ x₁ (one_cube₁ (act.act a)) I
    · exact eSec_cφ x₂ (one_cube₂ (act.act (H.bar a))) I
  obtain ⟨t, ht, -⟩ := exists_gen PP.isLB (formEq_drop (ε₀ := cε) (G2 G).hom (eSec (G2 G)) (eSec G) hz) c' hc'
  exact lbIso_of_gen PP.isLB x₁ x₂ t ht

end GlobalTheory.ExtAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGenStatement
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  first | exact @GlobalTheory.HodgeFrameGen.gen_isGen | exact GlobalTheory.HodgeFrameGen.gen_isGen | (intros; apply GlobalTheory.HodgeFrameGen.gen_isGen <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullbackStatement
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_frame_generator_value_pullback : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.val_gen_pull | exact GlobalTheory.HodgeFrameGen.val_gen_pull | (intros; apply GlobalTheory.HodgeFrameGen.val_gen_pull <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateConstantEverywhere
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section
namespace GlobalTheory.HTConstModel

theorem val_vw_eq_of_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ)
    {C : Type} [Field C] (v : Valuation C NNReal) {a b : C} (ha : a ≠ 0) (hb : b ≠ 0) {M : ℕ} (hM : 1 ≤ M) {n : ℤ}
    (h : v a ^ M = v b ^ n) {κ : ℝ} (hκ : val_vw la p v b = (κ : EReal)) :
    val_vw la p v a = (((n : ℝ) / M * κ : ℝ) : EReal) := by
  rw [val_vw_of_ne la p v hb, EReal.coe_eq_coe_iff] at hκ
  rw [val_vw_of_ne la p v ha, EReal.coe_eq_coe_iff, ← hκ]
  have hva : (0 : ℝ) < v a := by simpa [pos_iff_ne_zero] using ha
  have hvb : (0 : ℝ) < v b := by simpa [pos_iff_ne_zero] using hb
  have hl : (M : ℝ) * Real.log (v a) = n * Real.log (v b) := by
    have := congrArg (fun t : NNReal => Real.log (t : ℝ)) h
    simp only [NNReal.coe_pow, NNReal.coe_zpow] at this
    rwa [Real.log_pow, Real.log_zpow] at this
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have : Real.log (v a) = n / M * Real.log (v b) := by
    field_simp
    linarith
  rw [this]
  ring

end GlobalTheory.HTConstModel

theorem GlobalTheory.FlatCore.htConst_always : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne →
    GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → Always fun U x => HTConst U x := by
  intro hP h1 h2 h3 E _ _ _ H Dw l Xo c r U x hL Z τ s la
  obtain ⟨O, _, _, _, _, ϖ, hϖ, Zs, f, D, hInt, hNorm, hProp, hFlat, hLB, hT, sig, κ, hsig, hw⟩ :=
    GlobalTheory.T.archimedean_section_flat_weight hP h1 h2 h3 E H Dw l Xo c r U x hL Z τ s la
  have hconn := GlobalTheory.T.special_fibre_connected O Zs f hInt hNorm hProp hFlat
  obtain ⟨M, n, hM, -, hV⟩ :=
    GlobalTheory.T.prop_z_statement O ϖ hϖ Zs f D ⟨hInt, hNorm, hProp, hFlat, hconn, hLB, hT⟩ sig hsig
  refine ⟨(n : ℝ) / M * κ, fun w hw' => ?_⟩
  obtain ⟨p, _, R, _, _, φ, hv, hφi, hφl, ybar, y, e, cc, hyb, hy, he, hco, hval, hκ⟩ := hw w hw'
  have h := (hV R ℂ_[p] NNReal (Valued.v : Valuation ℂ_[p] NNReal) hv φ hφi hφl ybar hyb y hy).2 e cc he hco
  have hb : algebraMap R ℂ_[p] (φ ϖ) ≠ 0 := fun h0 =>
    hϖ.ne_zero (hφi ((hv.hom_inj (h0.trans (map_zero _).symm)).trans (map_zero φ).symm))
  rw [hval]
  exact GlobalTheory.HTConstModel.val_vw_eq_of_pow la p _ cc.ne_zero hb hM h hκ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_endomorphism_image_commutes_base_change : ∀ (S' T : Scheme.{0}) (g : T ⟶ S') (A G : Over S') [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G) (ε : A ⟶ A) (A' G' : Over T) [GrpObj A'] [IsCommMonObj A'] [GrpObj G'] [IsCommMonObj G'] (inc' : G' ⟶ A') (pr' : A' ⟶ G') (ε' : A' ⟶ A') (ψ : A'.left ⟶ A.left) (ψ₂ : (G2 A').left ⟶ (G2 A).left), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = ε → IsMonHom inc' → IsMonHom pr' → inc' ≫ pr' = 𝟙 G' → pr' ≫ inc' = ε' → IsGrpPullback A' A g ψ → IsSquare ψ ψ₂ → ε'.left ≫ ψ = ψ ≫ ε.left → ∃ (φ : G'.left ⟶ G.left) (φ₂ : (G2 G').left ⟶ (G2 G).left), IsGrpPullback G' G g φ ∧ IsSquare φ φ₂ ∧ inc'.left ≫ ψ = φ ≫ inc.left ∧ (inc' ⊗ₘ inc').left ≫ ψ₂ = φ₂ ≫ (inc ⊗ₘ inc).left := by
  first | (exact @GlobalTheory.ImgPB.image_idem_pullback) | (exact GlobalTheory.ImgPB.image_idem_pullback) | (intros; apply GlobalTheory.ImgPB.image_idem_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSemiAbelianHomRetractStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_semiAbelian_hom_retract : ∀ (S : Scheme.{0}) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G), IsAbelianScheme A → IsSemiAbelian G → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme G := by
  first | (exact @GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian) | (exact GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian) | (intros; apply GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_dense_genericFibre_normalisation : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  first | exact @GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization | exact GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization | (intros; apply GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDualStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Injective (T.map q) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧ Module.finrank k G.omega = Module.finrank k H.omega ∧ Module.finrank k G.dual.omega = Module.finrank k H.dual.omega := by
  first | exact @GlobalTheory.Dieu.isog_finrank_omega | exact GlobalTheory.Dieu.isog_finrank_omega | (intros; apply GlobalTheory.Dieu.isog_finrank_omega <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBijectiveOnTorsionCoprimeDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory

theorem isogeny_torsion_bij {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) (mu : B ⟶ A) (d M : ℕ) (T : Over S) :
    IsMonHom la → IsMonHom mu → la ≫ mu = 𝟙 A ^ d → mu ≫ la = 𝟙 B ^ d → M.Coprime d →
      (∀ y : T ⟶ A, y ^ M = 1 → y ≫ la = 1 → y = 1) ∧
        (∀ g : T ⟶ B, g ^ M = 1 → ∃ y : T ⟶ A, y ^ M = 1 ∧ y ≫ la = g) := by
  intro hla hmu hlm hml hMd
  refine ⟨fun y hyM hyl => ?_, fun g hgM => ?_⟩
  · have hyd : y ^ d = 1 := by
      have h1 : y ≫ (la ≫ mu) = y ^ d := by
        rw [hlm, MonObj.comp_pow, Category.comp_id]
      rw [← h1, ← Category.assoc, hyl, MonObj.one_comp]
    have h := (pow_gcd_eq_one (a := y) (m := M) (n := d)).2 ⟨hyM, hyd⟩
    rwa [Nat.Coprime.gcd_eq_one hMd, pow_one] at h
  ·
    set e := d ^ (Nat.totient M - 1) with he
    have hde : d * e % M = 1 % M := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · subst h0
        have hd1 : d = 1 := (Nat.coprime_zero_left d).1 hMd
        subst hd1
        simp [he]
      · have ht : 0 < Nat.totient M := Nat.totient_pos.2 hpos
        have hpow : d * e = d ^ Nat.totient M := by
          rw [he, ← pow_succ']
          congr 1
          omega
        rw [hpow]
        exact Nat.ModEq.pow_totient (Nat.Coprime.symm hMd)
    refine ⟨(g ≫ mu) ^ e, ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, ← MonObj.pow_comp, hgM, MonObj.one_comp, one_pow]
    · have h1 : (g ≫ mu) ≫ la = g ^ d := by
        rw [Category.assoc, hml, MonObj.comp_pow, Category.comp_id]
      rw [MonObj.pow_comp, h1, ← pow_mul, pow_eq_pow_mod (d * e) hgM, hde,
        ← pow_eq_pow_mod 1 hgM, pow_one]

end GlobalTheory
end

