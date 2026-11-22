import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPolAV
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PowPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.SiegelPower

def siegLam (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] (P : PolAV (Sp R)) [IsCommMonObj P.A] :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := P.A
  ab := P.isAb
  P := abelian₂ P.A P.L
  isLB := LB.isLB_linComb P.isLB _ _
  rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG P.isAb (pull_isLB (LB.isLB_linComb P.isLB _ _) _) _

theorem det_eq_one {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (hpd : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef)
    (hdet : IsUnit (W + W.transpose).det) : (W + W.transpose).det = 1 := by
  have h₁ := hpd.det_pos
  have h₂ : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).det = (((W + W.transpose).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [h₂] at h₁
  rcases Int.isUnit_iff.1 hdet with h | h
  · exact h
  · rw [h] at h₁; norm_num at h₁

theorem exists_pow_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ P.A)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ P'.g = r * P.g ∧ LBIso P'.L (LB.LinComb P.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ P r W hpd hdet
  have := P.isAb.comm
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLam hG P
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hfin : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := inferInstanceAs (IsFinite (𝟙 P.A.left))
  have hamp : RelAmple c.A c.diag := by
    have e := lbIso_diag L₁ P
    have h := relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB hfin
    exact (relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) (lbPow P.L 2) 1 one_pos P.isAb P.isAb
      (LB.isLB_linComb P.isLB _ _) hfin).2.2.2 _ hD e (h.2.1.2 P.ample)
  let G := Out.powObj P.A r
  let pr : Fin r → (G ⟶ P.A) := Out.powPr P.A
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ P.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit P.A r).lift (Fan.mk T y), fun u => (Out.powIsLimit P.A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit P.A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme P.A P.isAb r
            g := r * P.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r P.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit P.A r⟩, rfl, ?_⟩
  refine lbIso_nested P.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls P.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls P.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.PowPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_over_source_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over | exact GlobalTheory.Discrepancy.DivOver.exists_over | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceOfBirational
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_complex : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro X Y _ _ p s _ hs E
  exact DivOver.exists_over ℂ X Y p s hs E

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirationalStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_over_target_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective | exact GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetOfBirational
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_of_bijective_complex : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E :=
  fun p s _ hb E' => DivOver.exists_over_of_bijective ℂ _ _ p s hb E'

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemRingKrullDimQuotientEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_not_mem_ringKrullDim_quotient_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h : R), h ≠ 0 → h ∈ IsLocalRing.maximalIdeal R → ∃ q : Ideal R, q.IsPrime ∧ h ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by
  first | exact @GlobalTheory.exists_prime_notMem_ringKrullDim_quotient_eq_one | exact GlobalTheory.exists_prime_notMem_ringKrullDim_quotient_eq_one | (intros; apply GlobalTheory.exists_prime_notMem_ringKrullDim_quotient_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveLatticeMultiplier
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrderPrimitive

theorem exists_primitive_mul_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ b : E, (∀ x ∈ L, b * x ∈ L) ∧ IntermediateField.adjoin ℚ {b} = ⊤ := by
  intro E _ _ _ I _ φ L 𝔠 X U
  classical
  set g := Module.finrank ℚ (FR E) with hg
  let emb : E →ₗ[ℚ] (Fin g → ℂ) :=
    { toFun := fun x j => φ (U.e j) x
      map_add' := fun x x' => by funext j; simp
      map_smul' := fun q x => by funext j; simp [Rat.smul_def] }
  have hemb : ∀ x j, emb x j = φ (U.e j) x := fun _ _ => rfl
  have hdc : ∀ x, (fun j => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (U.e j)) = emb x := fun x => by
    funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, hemb]
  have hdim : Module.finrank ℚ E ≤ 2 * g := by
    rw [hg, ← Module.finrank_mul_finrank ℚ (FR E) E, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have hgpos : 0 < g := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have hinj : Function.Injective emb := fun x y hxy => by
    have := congrFun hxy ⟨0, hgpos⟩
    rw [hemb, hemb] at this
    exact (φ (U.e ⟨0, hgpos⟩)).injective this
  let f : E →ₗ[ℤ] (Fin g → ℂ) := emb.toAddMonoidHom.toIntLinearMap
  have hf : ∀ x, f x = emb x := fun _ => rfl
  have hfinj : Function.Injective f := hinj
  let K : Submodule ℤ E := U.u.Λ.comap f
  have hmemK : ∀ x, x ∈ K ↔ x ∈ L := fun x => by
    show emb x ∈ U.u.Λ ↔ x ∈ L
    rw [U.lat]
    constructor
    · rintro ⟨x', hx', h⟩
      rw [hdc] at h
      exact hinj h ▸ hx'
    · intro hx
      exact ⟨x, hx, (hdc x).symm⟩
  have hmap : Submodule.map f K = U.u.Λ := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hw
      obtain ⟨x, hx, rfl⟩ := (U.lat w).1 hw
      exact ⟨x, (hmemK x).2 hx, by rw [hf, hdc]⟩
  haveI : DiscreteTopology U.u.Λ := U.u.discrete
  haveI : IsZLattice ℝ U.u.Λ := ⟨U.u.full⟩
  have hΛfin : U.u.Λ.FG := Module.Finite.iff_fg.1 (ZLattice.module_finite ℝ U.u.Λ)
  have hKfg : K.FG := Submodule.fg_of_fg_map_injective f hfinj (hmap ▸ hΛfin)
  obtain ⟨T, hTfin, hTspan⟩ := Submodule.fg_def.1 hKfg
  have hsp : Submodule.span ℝ (emb '' (K.toAddSubgroup : Set E)) = ⊤ := by
    have : emb '' (K.toAddSubgroup : Set E) = (U.u.Λ : Set (Fin g → ℂ)) := by
      rw [← hmap]
      ext w
      simp [hf]
    rw [this]
    exact U.u.full
  have full : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ K.toAddSubgroup :=
    GlobalTheory.PeriodLattice.exists_nsmul_mem K.toAddSubgroup emb hdim hsp
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element ℚ E
  choose N hNpos hNmem using fun x : E => full (β * x)
  let Tf := hTfin.toFinset
  let n : ℕ := ∏ t ∈ Tf, N t
  have hnpos : 0 < n := Finset.prod_pos fun t _ => hNpos t
  have hmul : ∀ t ∈ T, (n : E) * β * t ∈ K := by
    intro t ht
    have htT : t ∈ Tf := hTfin.mem_toFinset.2 ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N htT
    have e : (n : E) * β * t = m • (N t • (β * t)) := by
      rw [smul_smul, nsmul_eq_mul, mul_comm m, ← hm, _root_.mul_assoc]
    rw [e]
    exact K.smul_of_tower_mem m (hNmem t)
  refine ⟨(n : E) * β, fun x hx => ?_, ?_⟩
  · have hxK : x ∈ K := (hmemK x).2 hx
    have hle : Submodule.span ℤ T ≤ K.comap (LinearMap.mulLeft ℤ ((n : E) * β)) := by
      refine Submodule.span_le.2 fun t ht => ?_
      exact hmul t ht
    rw [hTspan] at hle
    exact (hmemK _).1 (hle hxK)
  · have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
    refine top_unique (hβ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)
    have e : β = algebraMap ℚ E ((n : ℚ)⁻¹) * ((n : E) * β) := by
      rw [← _root_.mul_assoc, map_inv₀, map_natCast, inv_mul_cancel₀ (by exact_mod_cast hnpos.ne'), _root_.one_mul]
    have h2 := mul_mem (IntermediateField.algebraMap_mem (IntermediateField.adjoin ℚ {(n : E) * β}) ((n : ℚ)⁻¹))
      (IntermediateField.mem_adjoin_simple_self ℚ ((n : E) * β))
    rwa [← e] at h2

end GlobalTheory.OrderPrimitive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationGenericFibreTwoTorsio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwistAV

open GlobalTheory.CechPic (cls pull)

section

variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G]

def genSec (a : 𝟙_ (Over (Sp R)) ⟶ G) : 𝟙_ (Over (Sp (FractionRing R))) ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by
    rw [Category.assoc, Over.w a]; simp)) (pullback.lift_snd _ _ _)

theorem genSec_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (genSec a).left ≫ pullback.fst G.hom (jK R) = jK R ≫ a.left :=
  pullback.lift_fst _ _ _

theorem const_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (toUnit ((Over.pullback (jK R)).obj G) ≫ genSec a).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ G.hom ≫ a.left := by
  rw [Over.comp_left, Category.assoc, genSec_fst, ← Category.assoc (pullback.fst G.hom (jK R)), pullback.condition]
  rfl

theorem hom_ext_gen {T : Over (Sp (FractionRing R))} {x y : T ⟶ (Over.pullback (jK R)).obj G}
    (h : x.left ≫ pullback.fst G.hom (jK R) = y.left ≫ pullback.fst G.hom (jK R)) : x = y :=
  Over.OverMorphism.ext ((isGrpPullback_pullback G (jK R)).1.hom_ext h (by
    show x.left ≫ ((Over.pullback (jK R)).obj G).hom = y.left ≫ ((Over.pullback (jK R)).obj G).hom
    rw [Over.w, Over.w]))

theorem genSec_sq (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) : genSec a * genSec a = 1 := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let T : Over (Sp (FractionRing R)) := 𝟙_ _
  let x₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ a
  have hx : x₀.left = (genSec a).left ≫ pullback.fst G.hom (jK R) := by
    rw [genSec_fst]; rfl
  have e := hp T (genSec a) (genSec a) x₀ x₀ hx hx
  have haa : x₀ * x₀ = toUnit _ ≫ η[G] := by
    rw [← MonObj.comp_mul, ← sq, ha, Hom.one_def, ← Category.assoc, comp_toUnit]
  set c := genSec a * genSec a with hc
  let y₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ η[G]
  have hy : y₀.left = c.left ≫ pullback.fst G.hom (jK R) := by rw [show y₀ = x₀ * x₀ from haa.symm, e]
  have e₂ := hp T c c y₀ y₀ hy hy
  have hyy : y₀ * y₀ = y₀ := by
    rw [show y₀ = 1 from Hom.one_def.symm, _root_.one_mul]
  have hcc : c * c = c := hom_ext_gen (by rw [← e₂, hyy, hy])
  exact mul_eq_left.1 hcc

theorem transl_fst [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (GlobalTheory.PolTranslate.transl (genSec a)).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let GK := (Over.pullback (jK R)).obj G
  let p : Over.mk (GK.hom ≫ jK R) ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
  have e := hp GK (𝟙 GK) (toUnit GK ≫ genSec a) p (p ≫ toUnit G ≫ a) (by simp [p])
    (by rw [const_fst]; rfl)
  have e' : p * (p ≫ toUnit G ≫ a) = p ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [MonObj.comp_mul, Category.comp_id, _root_.mul_comm]
  rw [e', Over.comp_left] at e
  exact e.symm

end

theorem exists_translate_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D A G _ _ _ U a ha P hP
  haveI := U.gen_hom
  haveI := A.isAb.comm
  haveI : IsProper A.A.hom := A.isAb.proper
  let b := genSec a
  let a' : 𝟙_ (Over (Sp (FractionRing R))) ⟶ A.A := b ≫ U.gen.hom
  have ha' : a' * a' = 1 := by
    show (b ≫ U.gen.hom) * (b ≫ U.gen.hom) = 1
    rw [← MonObj.mul_comp, genSec_sq a ha, Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  let A₂ : PolAV (Sp (FractionRing R)) :=
    { A := A.A
      isAb := A.isAb
      g := A.g
      smoothDim := A.smoothDim
      L := GlobalTheory.RigidTranslate.rigTransl A.L a'
      isLB := LB.isLB_linComb A.isLB _ _
      rigid := GlobalTheory.RigidTranslate.rigidified_rigTransl A.isLB
      sym := GlobalTheory.RigidTranslate.sym_rigTransl ha' A.isLB A.sym
      ample := GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section a' A.isLB A.ample
      ktriv := GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ _ _ A.isLB a' A.ktriv }
  refine ⟨A₂, U.gen, U.gen_hom, ?_⟩
  let f := pullback.fst G.hom (jK R)
  let τ := ((toUnit G ≫ a) * 𝟙 G).left
  have hLG := U.LG.isLB
  have hext : pull U.gen.hom.left (cls A.L A.isLB) = pull f (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB A.isLB _) (pull_isLB hLG _)).2 U.ext
  have hP' : cls P.L.L P.L.isLB = pull τ (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff P.L.isLB (pull_isLB hLG _)).2 hP
  have hrig : pull (eSec G) (cls P.L.L P.L.isLB) = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB P.L.isLB _)).2 ⟨P.L.rig, P.L.rigGen⟩
  have ea : a.left = eSec G ≫ τ := by
    show a.left = (η[G] ≫ ((toUnit G ≫ a) * 𝟙 G)).left
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id,
      h1, _root_.mul_one]
  have hgt : U.gen.hom.left ≫ (GlobalTheory.PolTranslate.transl a').left =
      (GlobalTheory.PolTranslate.transl b).left ≫ U.gen.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PolTranslate.comp_transl, GlobalTheory.PolTranslate.transl, MonObj.mul_comp,
      Category.id_comp]
    rfl
  have hgc : U.gen.hom.left ≫ (toUnit A.A ≫ a').left = (toUnit _ ≫ b).left ≫ U.gen.hom.left := by
    rw [GlobalTheory.RigidTranslate.comp_const, ← Over.comp_left]
    rfl
  have h₁ := pull_isLB (LB.isLB_linComb A.isLB (K := Fin 2)
    ![(GlobalTheory.PolTranslate.transl a').left, (toUnit A.A ≫ a').left] ![1, -1]) U.gen.hom.left
  refine (GlobalTheory.CechPic.cls_eq_iff h₁ (pull_isLB P.L.isLB _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull _ _ h₁, GlobalTheory.CechPic.cls_linComb A.isLB, GlobalTheory.CechPic.cls_pull P.L.isLB]
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg, map_sub]
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, hgt, hgc, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_comp, hext,
      ← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, transl_fst a, const_fst a, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp f, GlobalTheory.CechPic.pull_comp, ea, GlobalTheory.CechPic.pull_comp, ← hP', hrig, map_zero, map_zero, sub_zero]
  · exact LB.isLB_linComb A.isLB _ _

end GlobalTheory.TwistAV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGroupOLinearTorsionLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_group_oLinear_torsion_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  first | (exact @GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (exact GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (intros; apply GlobalTheory.UPel.HT.LevPull.exists_pull_level  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutFaithfullyFlat
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pushout_faithfullyFlat : ∀ (R : Type) [CommRing R] (D D' E : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] D') (φ : D →ₐ[R] E), (ψ : D →+* D').FaithfullyFlat → ∃ (E' : Type) (_ : CommRing E') (_ : Algebra R E') (ψ' : E →ₐ[R] E') (φ' : D' →ₐ[R] E'), (ψ' : E →+* E').FaithfullyFlat ∧ ψ'.comp φ = φ'.comp ψ := by
  intro R _ D D' E _ _ _ _ _ _ ψ φ hψ
  letI : Algebra D E := φ.toRingHom.toAlgebra
  letI : Algebra D D' := ψ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  let f : E →+* TensorProduct D E D' := Algebra.TensorProduct.includeLeftRingHom
  let g : D' →+* TensorProduct D E D' := (Algebra.TensorProduct.includeRight : D' →ₐ[D] _).toRingHom
  have hfg : f.comp (algebraMap D E) = g.comp (algebraMap D D') :=
    RingHom.ext fun d => by
      change (algebraMap D E d) ⊗ₜ[D] (1 : D') = (1 : E) ⊗ₜ[D] algebraMap D D' d
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  letI iR : Algebra R (TensorProduct D E D') := (f.comp (algebraMap R E)).toAlgebra
  have hf : f.FaithfullyFlat := by
    have : Module.FaithfullyFlat E (TensorProduct D E D') := inferInstance
    exact (RingHom.faithfullyFlat_algebraMap_iff).2 this
  refine ⟨TensorProduct D E D', inferInstance, iR,
    { f with commutes' := fun r => rfl },
    { g with commutes' := fun r => ?_ }, hf, ?_⟩
  · change g (algebraMap R D' r) = f (algebraMap R E r)
    rw [← ψ.commutes r, ← φ.commutes r]
    exact (congrArg (fun h => h (algebraMap R D r)) hfg).symm
  · ext d
    exact congrArg (fun h => h d) hfg

end GlobalTheory
end

