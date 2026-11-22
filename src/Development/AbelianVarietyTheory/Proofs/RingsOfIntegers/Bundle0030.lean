import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0027
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MapsAtIdIsoPow
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowDegPre

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J] (F : J → (X' ⟶ X)) (q : Y ⟶ X')
  (n : ℤ)

def genOfPullBoxPow
    (a : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n))) :
    LB.Gen (LB.LinComb L (fun i => q ≫ F i) (fun _ => n)) where
  s := fun jN => res (wchart_comp_le_pull L F q jN) (a.s (fun _ => jN))

private lemma res_res_eq_pullU_pow_mul_res_of_res_eq {Y Z : Scheme.{0}} (q : Y ⟶ Z) {O : Z.Opens} (g : Γ(Z, O)ˣ) (n : ℤ)
    {U1 U2 D V : Y.Opens} (s1 : Γ(Y, U1)ˣ) (s2 : Γ(Y, U2)ˣ)
    (hD1 : D ≤ U1) (hE : D ≤ q ⁻¹ᵁ O) (hD2 : D ≤ U2)
    (h : res hD1 s1 = (∏ _x : PUnit, res hE (pullU q O g) ^ n) * res hD2 s2)
    (hB : V ≤ U1) (hA : q ⁻¹ᵁ O ≤ V) (hC : q ⁻¹ᵁ O ≤ U2) (hDO : q ⁻¹ᵁ O ≤ D) :
    res hA (res hB s1) = pullU q O g ^ n * res hC s2 := by
  have h2 := congrArg (res hDO) h
  simp only [map_mul, map_zpow, Fintype.prod_unique, res_res'] at h2
  have hid : ∀ (k : q ⁻¹ᵁ O ≤ q ⁻¹ᵁ O) (x : Γ(Y, q ⁻¹ᵁ O)ˣ), res k x = x :=
    fun k x => (res_res' k k x).symm.trans (res_of_le_of_le k k x)
  rw [res_res', h2, hid]

theorem mapsAt_idIso_pow
    (a : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n)))
    (ha : a.IsGen) :
    GeneratorPullback.MapsAt L (LB.LinComb L F (fun _ => 1)) F (CubePf.idIsoL _) q n a
      (genOfPullBoxPow L F q n a) := by
  intro jN jL
  have h := ha (fun _ => jN) (fun _ => jL)
  simp only [CubePf.idIsoL, genOfPullBoxPow]
  refine res_res_eq_pullU_pow_mul_res_of_res_eq q ((L.LinComb F fun _ => 1).g jN jL) n (a.s fun _ => jN) (a.s fun _ => jL) _ _ _ h _ _ _ ?_
  intro y hy
  have hy' := TopologicalSpace.Opens.mem_inf.1 (show q.base y ∈ _ from hy)
  exact TopologicalSpace.Opens.mem_inf.2
    ⟨Set.mem_iInter.2 fun _ => hy'.1, Set.mem_iInter.2 fun _ => hy'.2⟩

variable (r : J → (Y ⟶ X)) (he : ∀ i, q ≫ F i = r i)
  (t : ∀ i, LB.Gen (LB.LinComb L (K := PUnit) (fun _ => r i) (fun _ => n)))

def boxAt : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n)) :=
  GeneratorPullback.boxGen L F (fun _ => q) (fun _ => n) fun i =>
    GeneratorPullback.pullAlong L (F i) (𝟙 Y) (fun _ => r i) (fun _ => n) (fun _ => q)
      (fun _ => (he i).trans (Category.id_comp _).symm) (t i)

theorem isGen_boxAt (ht : ∀ i, (t i).IsGen) : (boxAt L F q n r he t).IsGen := by
  unfold boxAt
  exact isGen_boxGen L F _ _ _ fun i =>
    LBxP.isGen_pullAlong L (F i) (𝟙 Y) _ _ _ _ (t i) (ht i)

private lemma res_pullU_id_eq_res_of_le {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (h' : V ≤ U)
    (x : Γ(Y, U)ˣ) : res h (pullU (𝟙 Y) U x) = res h' x := by
  ext
  simp [res, pullU]
  rfl

private lemma res_res_prod_res_pullU_id_eq_res_prod {Y : Scheme.{0}} {J : Type} [Fintype J] {O T : J → Y.Opens}
    {W V Z W' : Y.Opens} (x : ∀ i, Γ(Y, O i)ˣ) (hD : ∀ i, T i ≤ (𝟙 Y) ⁻¹ᵁ O i) (hC : ∀ i, W ≤ T i)
    (hB : V ≤ W) (hA : Z ≤ V) (hG : ∀ i, W' ≤ O i) (hE : Z ≤ W') :
    res hA (res hB (∏ i, res (hC i) (res (hD i) (pullU (𝟙 Y) (O i) (x i))))) =
      res hE (∏ i, res (hG i) (x i)) := by
  simp only [map_prod, res_res']
  exact Finset.prod_congr rfl fun i _ => res_pullU_id_eq_res_of_le _ _ (x i)

theorem corr_boxAt :
    LB.Gen.Corr L _ _ _ _ (genOfPullBoxPow L F q n (boxAt L F q n r he t))
      (GeneratorPullback.finProdGen L (J := J) (fun i _ => r i) (fun _ _ => n) t) := by
  intro j j' hj hj' hjj
  have hj'' : j' = fun p => j p.1 := funext fun p => (hjj p.1 p (he p.1)).symm
  subst hj''
  simp only [genOfPullBoxPow, boxAt, GeneratorPullback.boxGen, GeneratorPullback.pullAlong, GeneratorPullback.finProdGen]
  exact res_res_prod_res_pullU_id_eq_res_prod (fun i => (t i).s fun _ => j i) _ _ _ _ _ _

end General

section Points

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)

def tuple {T : Over S} (x : Fin j → (T ⟶ G)) : T ⟶ G' := p.lim.lift (Fan.mk T x)

theorem tuple_pr {T : Over S} (x : Fin j → (T ⟶ G)) (i : Fin j) : tuple p x ≫ p.pr i = x i := by
  simpa [tuple] using p.lim.fac (Fan.mk T x) ⟨i⟩

theorem pt_ext {T : Over S} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b := by
  refine p.lim.hom_ext fun k => ?_
  obtain ⟨k⟩ := k
  simpa using h k

theorem lift_mul_pr {T : Over S} (a b : T ⟶ G') (i : Fin j) :
    (lift a b ≫ μ[G']) ≫ p.pr i = lift (a ≫ p.pr i) (b ≫ p.pr i) ≫ μ[G] := by
  have := p.hom i
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem eSec_pr (i : Fin j) : η[G'].left ≫ (p.pr i).left = η[G].left := by
  have := p.hom i
  rw [← Over.comp_left, IsMonHom.one_hom]

end Points

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (j : ℕ)

abbrev pw : IsPowGrp (powPol D.P j).A D.P.A j := (isPowPolAV_powPol D.P j).toIsPowGrp

theorem ptK_tuple_pr (x : Fin j → D.X) (i : Fin j) :
    ptK (tuple (pw D j) fun i => D.c (x i)) ≫ ((pw D j).pr i).left = ptK (D.c (x i)) := by
  unfold ptK
  rw [← Over.comp_left, Category.assoc, tuple_pr]

def pow : DegPre R where
  P := powPol D.P j
  rig := boxRig (pw D j) D.P.L D.rig
  rig_gen := boxRigIsGen _ _ _ j (pw D j) D.P.L D.rig D.P.isLB D.rig_gen
  cub := Classical.choose (boxCubical _ _ _ j (pw D j) ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub
    (powPol D.P j).isLB (boxRigIsGen _ _ _ j (pw D j) D.P.L D.rig D.P.isLB D.rig_gen))
  sym := boxSym (pw D j) D.P.L D.sym
  sym_gen := (boxSym_isSymmetry _ _ _ j (pw D j) D.P.L D.sym D.P.isLB D.sym_gen D.sym_rig).1
  sym_rig := (boxSym_isSymmetry _ _ _ j (pw D j) D.P.L D.sym D.P.isLB D.sym_gen D.sym_rig).2
  X := Fin j → D.X
  c := fun x => tuple (pw D j) fun i => D.c (x i)
  c_add := fun a b => pt_ext (pw D j) fun i => by
    refine (tuple_pr _ _ i).trans (Eq.trans ?_ (lift_mul_pr (pw D j) _ _ i).symm)
    rw [tuple_pr, tuple_pr]
    exact D.c_add _ _
  psi := fun x => boxAt D.P.L (fun i => ((pw D j).pr i).left) _ (-1) (fun i => ptK (D.c (x i)))
    (ptK_tuple_pr D j x) (fun i => D.psi (x i))
  psi_gen := fun x => isGen_boxAt _ _ _ _ _ _ _ fun i => D.psi_gen (x i)

def isPowDeg_pow : IsPowDeg (pow D j) D j where
  pw := pw D j
  w := CubePf.idIsoL (boxLB D.P.L (pw D j).pr)
  w_gen := CubePf.idIsoL_isGen (LB.isLB_linComb D.P.isLB _ _)
  w_rig := ⟨_, mapsAt_idIso_pow D.P.L _ _ 1 _ (pow D j).rig_gen,
    corr_boxAt D.P.L _ _ 1 (fun _ => eSec D.P.A) (eSec_pr (pw D j)) (fun _ => D.rig)⟩
  xe := AddEquiv.refl _
  c_pr := fun x i => tuple_pr (pw D j) _ i
  w_psi := fun x => ⟨_, mapsAt_idIso_pow D.P.L _ _ (-1) _ ((pow D j).psi_gen x),
    corr_boxAt D.P.L _ _ (-1) (fun i => ptK (D.c (x i))) (ptK_tuple_pr D j x) (fun i => D.psi (x i))⟩

theorem exists_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (j : ℕ),
    ∃ D' : DegPre R, Nonempty (IsPowDeg D' D j) := by
  intro R _ _ D j
  exact ⟨pow D j, ⟨isPowDeg_pow D j⟩⟩

end GlobalTheory.PowDegPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecBGeneratesOfIsUnit
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaLocalDomain

open GlobalTheory.IndivisibleSection

theorem vanish_of_terms_mem {R : Type} [CommRing R] [IsDomain R] {I I' : Ideal R} (hI : I ≤ I') {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α, ∃ a ∈ I' ^ (e + 1), ∃ f' : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom a (f α) f') (j) :
    ((fstG I' e G).left.app _).hom (σ.f j) = 0 := by
  have hle : I ^ (e + 1) ≤ I' ^ (e + 1) := Ideal.pow_right_mono hI _
  have hth : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)) ≫ thick R I e = thick R I' e := by
    simp only [thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (thickObj R I' e G).left ⟶ (thickObj R I e G).left, ρ ≫ fGl I G e = fGl I' G e :=
    ⟨pullback.lift (pullback.fst G.hom (thick R I' e))
      (pullback.snd G.hom (thick R I' e) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)))
      (by rw [Category.assoc, hth]; exact pullback.condition), pullback.lift_fst _ _ _⟩
  have hw : (ρ ≫ pGl U e) ≫ D.toPre.P.A.hom =
      pullback.snd G.hom (thick R I' e) ≫ spMap (Ideal.Quotient.mk (I' ^ (e + 1))) := by
    have w₁ : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
      (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
    rw [Category.assoc, w₁, ← Category.assoc, hρ]
    exact pullback.condition
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : (thickObj R I' e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hy' : (ρ ≫ fGl I G e) y ∈ U.LG.L.U jL := by rw [hρ]; exact Set.mem_iInter.1 hy 0
  have H := (hS _ ρ y J hJ).2 jL hy'
  have hz : ∀ α, sval (f α) (ρ ≫ pGl U e) y J = 0 := fun α => by
    obtain ⟨a, ha, f', hf'⟩ := h0 α
    have hc : cst ((ρ ≫ pGl U e) ≫ D.toPre.P.A.hom) y a = 0 := by
      rw [hw]
      refine (cst_comp _ _ y a).trans ?_
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, cst, map_zero]
      exact gs_zero _ y ⊤ trivial
    rw [sval_of_secIsMul hf' _ y hJ, hc, zero_mul]
  rw [Finset.sum_eq_zero fun α _ => by rw [hz α, zero_mul], hρ] at H
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_zero (𝟙 _) y _ hy).symm)
  rw [Category.id_comp]
  exact (Units.mul_right_eq_zero _).1 H

theorem secBGenerates_of_isUnit {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {k : ℕ}
    {α : D.toPre.X} {b g : D.toPre.SecB k α} (hb : SecBGenerates (D := D) k α b) {a₀ : R} (hu : IsUnit a₀)
    (ha₀ : SecIsMul D.toPre.P.A.hom a₀ g b) : SecBGenerates (D := D) k α g := by
  have hL := D.toPre.P.isLB
  have tr : ∀ {a c : R} {s t w : D.toPre.SecB k α}, SecIsMul D.toPre.P.A.hom a s t →
      SecIsMul D.toPre.P.A.hom c t w → SecIsMul D.toPre.P.A.hom (a * c) s w := fun h h' =>
    secIsMul_of_sval hL fun y J hJ => by
      rw [sval_of_secIsMul h _ y hJ, sval_of_secIsMul h' _ y hJ, Category.id_comp, cst_mul', _root_.mul_assoc]
  obtain ⟨u, rfl⟩ := hu
  have hinv : SecIsMul D.toPre.P.A.hom (↑u⁻¹ : R) b g := secIsMul_of_sval hL fun y J hJ => by
    rw [sval_of_secIsMul ha₀ _ y hJ, Category.id_comp, ← _root_.mul_assoc, ← cst_mul', Units.inv_mul, cst_one',
      _root_.one_mul]
  intro s
  obtain ⟨a, ha, hau⟩ := hb s
  refine ⟨a * ↑u⁻¹, tr ha hinv, fun a' ha' => ?_⟩
  rw [← hau _ (tr ha' ha₀), Units.mul_inv_cancel_right]

theorem main : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (s : H0 U.LG.L 1), NonzeroOnSpecial U s → IsTheta U s := by
  intro hLaws R _ _ _ _ I hI D A G _ _ U s hs
  obtain ⟨sK, hsK⟩ := exists_pull_val U.LG.isLB s (pullback.fst G.hom (jK R))
    (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by simp only [Category.comp_id])
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨g, hg, hgE⟩ := GlobalTheory.T.expansion_integralSection_integral_noetherianLocal R I hI D A G U.toUnifPre 1 s sK
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => (hsK _ _ y J hJ).symm) E hE
  obtain ⟨b, hb⟩ := exists_secBGenerates hLaws.secBaseChange R I D
  obtain ⟨a, ha, -⟩ := hb (g 0)
  have hu : IsUnit a := by
    by_contra hn
    obtain ⟨j, hj⟩ := hs
    refine hj (vanish_of_terms_mem hI U.toUnifPre 0 1 s g (hg 0) (fun α => ?_) j)
    rw [zero_add, pow_one]
    by_cases hα : α = 0
    · subst hα
      exact ⟨a, hn, b, ha⟩
    · obtain ⟨c, hc, g', hg'⟩ := GlobalTheory.LevelOneIdeal.main hLaws.globalFns R I D E g hgE α hα
      exact ⟨c, hI hc, g', hg'⟩
  exact fun e => ⟨g, hg e, secBGenerates_of_isUnit hb hu ha⟩

end GlobalTheory.ThetaLocalDomain
end
end

