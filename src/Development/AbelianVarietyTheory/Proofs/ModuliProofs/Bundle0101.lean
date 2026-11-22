import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

open TopologicalSpace

theorem exists_unit_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (a b : LB.Gen (LB.LinComb L φ ε)) (ha : a.IsGen) (hb : b.IsGen) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι), r z ∈ LB.wchart L φ q →
      gm r z (LB.wchart L φ q) (a.s q) = gm r z ⊤ u * gm r z (LB.wchart L φ q) (b.s q) := by
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι),
      gm r z (LB.wchart L φ q) (a.s q * (b.s q)⁻¹) =
        gm r z (LB.wchart L φ q) (a.s q) * (gm r z (LB.wchart L φ q) (b.s q))⁻¹ := fun Z r z q =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top) (fun y _ => by
      choose q hq using fun k => exists_chart hL (φ k y)
      exact Opens.mem_iSup.2 ⟨q, Set.mem_iInter.2 hq⟩) (fun q => a.s q * (b.s q)⁻¹) (fun q q' y hy => by
      refine (v _ _ y q).trans (Eq.trans ?_ (v _ _ y q').symm)
      rw [gen_trans ha (𝟙 Y) y hy.1 hy.2, gen_trans hb (𝟙 Y) y hy.1 hy.2, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r z q hq => ?_⟩
  rw [← gm_res r z (le_top : LB.wchart L φ q ≤ ⊤) hq u, hu q]
  exact ((congrArg (· * _) (v Z r z q)).trans (inv_mul_cancel_right _ _)).symm

theorem isPullCubical_of_iso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') (α : G' ⟶ G) [IsMonHom α] {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α.left)) :
    (CubeMap.ofHom α).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (𝟙 _) (fun _ => (CubeMap.ofHom α).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α.left) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α.left (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α.left).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S) ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α.left = (CubeMap.ofHom α).F3 ≫ thφ G (x3 G) I :=
      fun I => (CubeMap.ofHom α).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (CubeMap.ofHom α).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (CubeMap.ofHom α).F3 = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left := by
      show (e ≫ (α ⊗ₘ α ⊗ₘ α)).left = _
      simp only [e, lift_map, MonObj.one_comp]
    have b₁ := (isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1
    have b₂ := (isCub_cubV c' (T := 𝟙_ (Over S)) hJ').face 1 1
    have b₃ := prod_cub (1 : 𝟙_ (Over S) ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α.left)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

theorem mono_of_kTriv {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (α : G' ⟶ G) [IsMonHom α]
    {L' : LB G'.left} {L : LB G.left} (hL' : L'.IsLB) (hL : L.IsLB) (h : LBIso L' (L.pull α.left))
    (hK : Out.KTriv G' L') : Mono α.left := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (x : Over.mk t ⟶ G'), x ≫ α = 1 → x = 1 := by
    intro R _ t x hx
    refine hK R t x fun p => ⟨⊤, trivial, ?_⟩
    let φ' : Fin 2 → ((Over.mk t ⊗ G').left ⟶ G'.left) :=
      ![(lift (fst (Over.mk t) G' ≫ x) (snd (Over.mk t) G') ≫ μ[G']).left, (snd (Over.mk t) G').left]
    have e : φ' 0 ≫ α.left = φ' 1 ≫ α.left := by
      show (((fst (Over.mk t) G' ≫ x) * snd (Over.mk t) G') ≫ α).left = (snd (Over.mk t) G' ≫ α).left
      rw [MonObj.mul_comp, Category.assoc, hx, MonObj.comp_one, _root_.one_mul]
    obtain ⟨t₁, h₁, -⟩ := exists_gen hL (φ' := fun k => φ' k ≫ α.left) (ε' := ![1, -1]) (fun U _ k => by
      rw [Fin.prod_univ_two]; simp [e]) (LB.oneGen L (Y := (Over.mk t ⊗ G').left)) AbLaw.Cube.oneGen_isGen
    obtain ⟨t₂, h₂⟩ := exists_down ((isGen_iff w).1 hw) hL hL' t₁ h₁
    exact gen_chartPull (chartPullPull _ _ _ rfl) t₂ h₂
  refine ⟨fun {Z} f g hfg => ?_⟩
  refine Scheme.Cover.hom_ext Z.affineCover _ _ fun i => ?_
  have hs : g ≫ G'.hom = f ≫ G'.hom := by rw [← Over.w α, reassoc_of% hfg]
  let j : Spec (CommRingCat.of (Z.affineOpenCover.X i)) ⟶ Z := Z.affineCover.f i
  let x : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ f) (Category.assoc _ _ _)
  let y : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ g) (by rw [Category.assoc, hs]; rfl)
  have e : x ≫ α = y ≫ α := Over.OverMorphism.ext (by
    show (j ≫ f) ≫ _ = (j ≫ g) ≫ _
    rw [Category.assoc, hfg, Category.assoc])
  have := key _ _ (x * y⁻¹) (by rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel])
  exact congrArg (fun q => q.left) (mul_inv_eq_one.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem iso_of_lam {S : Scheme.{0}} (t' t : SAB H S) (α : t'.G ⟶ t.G) [IsMonHom α]
    (hact : ∀ a, t'.act.act a ≫ α = α ≫ t.act.act a)
    (h : LBIso (abelian₂ t'.G (lbPow t'.PP.L 1)) (abelian₂ t'.G (t.PP.L.pull α.left))) :
    LBIso t'.PP.L (t.PP.L.pull α.left) := by
  let U : t'.G ⟶ G2 t'.G := lift (𝟙 _) (t'.act.act H.w0)
  have ps : ∀ I : Finset (Fin 2), U ≫ psum t'.G (x2 t'.G) I = psum t'.G ![𝟙 _, t'.act.act H.w0] I := fun I =>
    (psum_hom (preHom U) (x2 t'.G) I).trans (congrArg (fun q => psum t'.G q I) (funext fun i => by
      fin_cases i <;> simp [preHom, U, x2]))
  have pa : ∀ I : Finset (Fin 2), psum t'.G ![𝟙 _, t'.act.act H.w0] I ≫ α = α ≫ psum t.G ![𝟙 _, t.act.act H.w0] I :=
    fun I => (psum_hom (MonoidHom.mk' (fun z : t'.G ⟶ t'.G => z ≫ α) fun a b => MonObj.mul_comp a b α) _ I).trans
      ((congrArg (fun q => psum t.G q I) (funext fun i => by
        fin_cases i <;> simp [preHom, hact])).trans (psum_hom (preHom α) ![𝟙 _, t.act.act H.w0] I).symm)
  have h₁ : LBIso (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (lbPow t'.PP.L 1))
      (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm)
      (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm) h
  have h₂ : LBIso (t'.PP.L.pull (𝟙 _)) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t'.PP.L.pull (𝟙 _))) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun I => by simp) t'.prim
  have h₃ : LBIso (t.PP.L.pull α.left) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ α.left fun I =>
      congrArg (fun q => q.left) (pa I.down)) t.prim
  have i₁ := pull_isLB t'.PP.isLB (𝟙 _)
  have i₂ := pull_isLB t.PP.isLB α.left
  have h₄ := LBIso.trans i₁ (DVR.linComb_isLB _ i₂ _ _) i₂
    (LBIso.trans i₁ (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ i₂ _ _) h₂ h₁) h₃.symm
  exact LBIso.chartPull (chartPullUnpull _ _ rfl) (chartPullId _) h₄

theorem pow_eq_one_of_weilIs (hK : Out.KerPowSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    {T : Over S} [Unique T.left] {n : ℕ} (hn : 0 < n) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) : x ^ n = 1 ∧ y ^ n = 1 := by
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, -⟩ := h default
  have key : ∀ θ : Out.ThetaGrp P.A P.L n (Out.overRes V), θ.pt ^ n = 1 := fun θ =>
    (hK S P n hn _ θ.pt).1 fun p => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) θ.φ θ.isGen⟩
  have hs : Surjective V.ι := ⟨fun z => ⟨⟨default, hV⟩, Subsingleton.elim _ _⟩⟩
  have he : Epi V.ι := Flat.epi_of_flat_of_surjective _
  have key₂ : ∀ z : T ⟶ P.A, (Out.overResι V ≫ z) ^ n = 1 → z ^ n = 1 := fun z hz => by
    rw [← MonObj.comp_pow, ← MonObj.comp_one (Out.overResι V)] at hz
    exact Over.OverMorphism.ext ((cancel_epi V.ι).1 (congrArg (fun q => q.left) hz))
  exact ⟨key₂ x (hx ▸ key θx), key₂ y (hy ▸ key θy)⟩

end GlobalTheory.HeckePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerMatrixLinearInDerivation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Lin

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}

theorem ksRel_add {D D' : R → ℂ} {Θ Θ' : Matrix (Fin g) (Fin g) ℂ}
    {s s' : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ}
    (h : KSRel u p m D Θ s) (h' : KSRel u p m D' Θ' s') :
    KSRel u p m (fun r => D r + D' r) (Θ + Θ') (fun z W f => s z W f + s' z W f) where
  der z :=
    { add := fun W hW f f' => by
        simp only [(h.der z).add W hW, (h'.der z).add W hW]
        ring
      mul := fun W hW f f' => by
        simp only [(h.der z).mul W hW, (h'.der z).mul W hW]
        ring
      res := fun W W' hle hW' f => by
        simp only [(h.der z).res W W' hle hW', (h'.der z).res W W' hle hW'] }
  base z r := by simp only [h.base, h'.base]
  hol W f := (h.hol W f).add (h'.hol W f)
  per l W f z hz := by
    simp only [h.per l W f z hz, h'.per l W f z hz, Matrix.add_mulVec, map_add]
    ring

theorem ksRel_smul (c : ℂ) {D : R → ℂ} {Θ : Matrix (Fin g) (Fin g) ℂ}
    {s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ} (h : KSRel u p m D Θ s) :
    KSRel u p m (fun r => c * D r) (c • Θ) (fun z W f => c * s z W f) where
  der z :=
    { add := fun W hW f f' => by
        simp only [(h.der z).add W hW]
        ring
      mul := fun W hW f f' => by
        simp only [(h.der z).mul W hW]
        ring
      res := fun W W' hle hW' f => by
        simp only [(h.der z).res W W' hle hW'] }
  base z r := by simp only [h.base]
  hol W f := (h.hol W f).const_mul c
  per l W f z hz := by
    simp only [h.per l W f z hz, Matrix.smul_mulVec, map_smul, smul_eq_mul]
    ring
end

theorem ks_linear : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  intro P₀ u Hm χ hG o R _ _ _ _ _ _ X p m hs hpb
  have hder : ∀ D : Derivation o R ℂ, IsDer (algebraMap R ℂ) (fun r => D r) := fun D =>
    ⟨fun a b => D.map_add a b, fun a b => by
      show D (a * b) = _
      rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]⟩
  have hex : ∀ D : Derivation o R ℂ, ∃ Θ s, KSRel u p m (fun r => D r) Θ s := fun D =>
    GlobalTheory.T.exists_analytic_kodairaSpencer_class P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ (hder D)
  choose Θ s hΘ using hex
  have huniq : ∀ (D : Derivation o R ℂ) Θ' s', KSRel u p m (fun r => D r) Θ' s' → Θ D = Θ' :=
    fun D Θ' s' h => GlobalTheory.KS.Uniq.ks_unique P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ _ _ _ _ (hΘ D) h
  refine ⟨{ toFun := Θ, map_add' := ?_, map_smul' := ?_ }, fun D => ⟨s D, hΘ D⟩⟩
  · intro D D'
    apply huniq (D + D')
    have e : (fun r => (D + D') r) = fun r => D r + D' r := funext fun _ => Derivation.add_apply _
    rw [e]
    exact ksRel_add (hΘ D) (hΘ D')
  · intro c D
    rw [RingHom.id_apply]
    apply huniq (c • D)
    have e : (fun r => (c • D) r) = fun r => c * D r := funext fun r => by
      rw [Derivation.smul_apply, smul_eq_mul]
    rw [e]
    exact ksRel_smul c (hΘ D)

end GlobalTheory.KS.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DlogPol

section Germs
variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {O₀ O : Y.Opens} (h : O ≤ O₀) (hz : r z ∈ O) (s : Γ(Y, O₀)) :
    gs r z O (rsT s O) = gs r z O₀ s := by
  rw [rsT, dif_pos h]
  exact gs_res r z h hz s

theorem gs_pbT (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {O₀ : X.Opens} {O : Y.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (hz : r z ∈ O)
    (s : Γ(X, O₀)) : gs r z O (pbT f s O) = gs (r ≫ f) z O₀ s := by
  rw [pbT, dif_pos h]
  exact (gs_res r z h hz ((f.app O₀).hom s)).trans (gs_pull r f z O₀ (h hz) s)

theorem gs_one (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) : gs r z O 1 = 1 := by
  simp only [gs_eq r z O hz, map_one]

theorem gs_sub (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a b : Γ(Y, O)) :
    gs r z O (a - b) = gs r z O a - gs r z O b := by
  simp only [gs_eq r z O hz, map_sub]

theorem gs_constFn {R : Type} [CommRing R] (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a : R) :
    gs r z O (constFn p O a) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (show O ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) hz ((p.app ⊤).hom _)).trans (gs_pull r p z ⊤ trivial _)

theorem eps_sq {K : Type} [Field K] (p : X ⟶ Sp (DualNumber K)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

end Germs

theorem exists_gen {K : Type} [Field K] {X Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber K)) (τ ρ : Y' ⟶ Y)
    (hτ : ∀ (y : Y') (W : Y.Opens), τ y ∈ W → ρ y ∈ W) (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (k : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hk : ∀ i j (y : Y'), m (τ y) ∈ L.U i → m (τ y) ∈ L.U j →
      gs (τ ≫ m) y _ (L.g i j).val = gs (ρ ≫ m) y _ (L.g i j).val *
        (1 + gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) *
          gs ρ y _ (k i j)))
    (hc : IsCob _ k) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) (fun n => ![τ, ρ] n ≫ m) ![1, -1]), t.IsGen := by
  obtain ⟨b, hb⟩ := hc
  let φ : Fin 2 → (Y' ⟶ X) := fun n => ![τ, ρ] n ≫ m
  have h₀ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (τ y) ∈ L.U (J 0) := fun J y hy =>
    Set.mem_iInter.1 hy 0
  have h₀' : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 0) := fun J y hy =>
    hτ y (m ⁻¹ᵁ L.U (J 0)) (h₀ J y hy)
  have h₁ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 1) := fun J y hy =>
    Set.mem_iInter.1 hy 1
  have le : ∀ J : Fin 2 → L.ι, LB.wchart L φ J ≤ (ρ ≫ m) ⁻¹ᵁ (L.U (J 0) ⊓ L.U (J 1)) := fun J y hy =>
    ⟨h₀' J y hy, h₁ J y hy⟩
  let u : ∀ J : Fin 2 → L.ι, Γ(Y', LB.wchart L φ J)ˣ := fun J =>
    ⟨1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _, 1 + constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _,
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J),
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J)⟩
  refine ⟨⟨fun J => res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J⟩, isGen_of_gm _ fun y J J' hJ hJ' => ?_⟩
  set e := gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) with he
  have ee : e * e = 0 := by
    rw [he, ← gs_mul π y ⊤ trivial, ← map_mul, DualNumber.eps_mul_eps, map_zero, gs_eq π y ⊤ trivial, map_zero, map_zero]
  have val : ∀ J : Fin 2 → L.ι, y ∈ LB.wchart L φ J →
      (gm (𝟙 Y') y (LB.wchart L φ J) (res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J)).val =
        (gm (ρ ≫ m) y _ (L.g (J 0) (J 1))).val * (1 - e * gs ρ y _ (b (J 0))) := fun J hJ => by
    rw [map_mul, Units.val_mul, gm_res (𝟙 Y') y (le J) hJ, gm_pull (𝟙 Y') (ρ ≫ m) y _ (le J hJ), Category.id_comp,
      ← gs_unit (𝟙 Y') y _ hJ]
    congr 1
    change gs (𝟙 Y') y _ (1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _) = _
    rw [gs_sub _ _ _ hJ, gs_one _ _ _ hJ, gs_mul _ _ _ hJ, gs_constFn _ _ _ _ hJ,
      gs_pbT (𝟙 Y') ρ y (O₀ := m ⁻¹ᵁ L.U (J 0)) (fun y hy => h₀' J y hy) hJ, Category.id_comp, Category.id_comp]
  have tr : trF φ ![1, -1] (𝟙 Y') y J J' =
      gm (τ ≫ m) y _ (L.g (J 0) (J' 0)) * (gm (ρ ≫ m) y _ (L.g (J 1) (J' 1)))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    simp only [Category.id_comp]
    simp [φ]
  have c₁ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₀' J' y hJ') (h₁ J' y hJ')
  have c₂ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₁ J y hJ) (h₁ J' y hJ')
  have k₁ := hk _ _ y (h₀ J y hJ) (h₀ J' y hJ')
  have m₀ : ρ y ∈ m ⁻¹ᵁ L.U (J 0) ⊓ m ⁻¹ᵁ L.U (J' 0) := ⟨h₀' J y hJ, h₀' J' y hJ'⟩
  rw [hb, gs_sub _ _ _ m₀, gs_rsT _ _ inf_le_right m₀, gs_rsT _ _ inf_le_left m₀,
    gs_unit (τ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) ⟨h₀ J y hJ, h₀ J' y hJ'⟩, gs_unit (ρ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) m₀, ← he] at k₁
  change gm (𝟙 Y') y (LB.wchart L φ J) _ = trF φ ![1, -1] (𝟙 Y') y J J' * gm (𝟙 Y') y (LB.wchart L φ J') _
  rw [tr, _root_.mul_assoc, mul_left_comm, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val J hJ, val J' hJ', k₁]
  have d := congrArg Units.val (c₁.trans c₂.symm)
  rw [Units.val_mul, Units.val_mul] at d
  linear_combination (-(1 - e * gs ρ y _ (b (J 0)))) * d +
    ((gm (ρ ≫ m) y _ (L.g (J 0) (J' 0))).val * (gm (ρ ≫ m) y _ (L.g (J' 0) (J' 1))).val *
      (gs ρ y _ (b (J' 0)) - gs ρ y _ (b (J 0))) * gs ρ y _ (b (J' 0))) * ee

theorem isUnit_pbT {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (i j : L.ι) :
    IsUnit (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) := by
  rw [pbT, dif_pos (show m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j) from fun _ h => h)]
  exact (L.g i j).isUnit.map _

theorem isCoc_dlog {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (d : ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (hmul : ∀ W f f', d W (f * f') = f * d W f' + f' * d W f)
    (hres : ∀ W W' (f : Γ(Y, W)), W' ≤ W → d W' (rsT f W') = rsT (d W f) W')
    (φ : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hφ : ∀ i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ i j =
      d _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))) : IsCoc _ φ := by
  intro i j k
  set O : Y.Opens := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k with hO
  let G : L.ι → L.ι → Γ(Y, O) := fun a b => rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) O
  have hd : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → d O (G a b) = G a b * rsT (φ a b) O := fun a b h => by
    rw [hres _ _ _ h, ← hφ]
    simp only [G, rsT, dif_pos h, map_mul]
  have hg : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → ∀ y ∈ O,
      gs (𝟙 Y) y O (G a b) = (gm m y _ (L.g a b)).val := fun a b h y hy => by
    rw [gs_rsT _ _ h hy, gs_pbT (𝟙 Y) m y (O₀ := L.U a ⊓ L.U b) (O := m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) (fun _ h => h) (h hy), Category.id_comp,
      gs_unit m y (L.U a ⊓ L.U b) (h hy)]
  have l₁ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j := inf_le_left
  have l₂ : O ≤ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.2, h.2⟩
  have l₃ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.1, h.2⟩
  have co : G i j * G j k = G i k := fn_ext fun y hy => by
    rw [gs_mul _ _ _ hy, hg _ _ l₁ y hy, hg _ _ l₂ y hy, hg _ _ l₃ y hy, ← Units.val_mul,
      gm_cocycle hL m y hy.1.1 hy.1.2 hy.2]
  have un : IsUnit (G i k) := by
    simp only [G, rsT, dif_pos l₃]
    exact (isUnit_pbT m L i k).map _
  have e := hmul O (G i j) (G j k)
  rw [co, hd _ _ l₁, hd _ _ l₂, hd _ _ l₃] at e
  refine un.mul_left_cancel ?_
  change G i k * (rsT (φ i j) O + rsT (φ j k) O) = G i k * rsT (φ i k) O
  linear_combination (-1 : Γ(Y, O)) * e - (rsT (φ i j) O + rsT (φ j k) O) * co

theorem preimage_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (w : epsR K ⟶ A) (hw : IsTangent w)
    (W : A.left.Opens) :
    ((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  let z : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hz : z ≫ w = η[A] := Over.OverMorphism.ext hw
  let j : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ z) (𝟙 A)
  have j₁ : j ≫ snd (epsR K) A = 𝟙 A := lift_snd _ _
  have j₂ : j ≫ ((fst (epsR K) A ≫ w) * snd (epsR K) A) = 𝟙 A := by
    rw [MonObj.comp_mul, j₁, lift_fst_assoc, Category.assoc, hz, ← Hom.one_def, _root_.one_mul]
  have j₃ : j.left ≫ (fst (epsR K) A).left = A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    have := congrArg (fun q => q.left) (lift_fst (toUnit A ≫ z) (𝟙 A))
    refine this.trans ?_
    change (toUnit A).left ≫ _ = _
    congr 1
  have h := (GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left j.left
    (IsPullback.of_hasPullback (epsR K).hom A.hom).flip (congrArg (fun q => q.left) j₁) j₃).1
    (((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W)
  rw [← h, ← Scheme.Hom.comp_preimage j.left, ← Over.comp_left, j₂]
  rfl

theorem dlog_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  intro K _ P g v dd hv hdd X m L hL ⟨u, hu⟩
  refine ⟨⟨fun a i j => ((isUnit_pbT m L i j).unit⁻¹ : _ˣ).val * dd a _ (pbT m (L.g i j).val _), fun a i j => ?_⟩,
    fun φ hφ => ⟨fun a => ?_, fun c hc => ?_⟩⟩
  · rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
  · obtain ⟨-, h₁, h₂, -⟩ := (GlobalTheory.KS.InvField.main K P.A (v a) (hv.1 a)).2 _ (hdd a)
    exact isCoc_dlog m L hL (dd a) h₁ h₂ (φ a) (hφ a)
  have := P.isAb.comm
  obtain ⟨a₁, a₂, a₃, -⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A g v hv.1
  obtain ⟨w, hw, -⟩ := a₁ c
  have tw := a₂ c w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.KS.InvField.main K P.A w tw).1
  have hsum : ∀ (W : P.A.left.Opens) (h : Γ(P.A.left, W)), dw W h = ∑ a, constFn P.A.hom _ (c a) * dd a W h :=
    GlobalTheory.KS.InvHom.invDer_along_hom K P.A P.A (𝟙 _) g v dd w dw c inferInstance hv.1 tw hdd hdw (by rwa [Category.comp_id])
  have pre := preimage_transl w tw
  set τ := ((fst (epsR K) P.A ≫ w) * snd (epsR K) P.A).left with hτ
  set ρ := (snd (epsR K) P.A).left with hρ
  obtain ⟨t, ht⟩ := exists_gen (fst (epsR K) P.A).left τ ρ (fun y W hy => (pre W).le hy) m L hL _ (fun i j y hi hj => by
    have hy : y ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) := (pre _).le ⟨hi, hj⟩
    have e := congrArg (gs (𝟙 _) y _) (hdw (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (pbT m (L.g i j).val _))
    have e₂ : dw _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) =
        pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * lc P.A.hom c φ i j := by
      rw [hsum, lc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [← hφ a i j, mul_left_comm]
    rw [e₂, gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy, gs_pbT _ _ _ (pre _).ge hy,
      gs_pbT _ _ _ le_rfl hy, gs_pbT _ _ _ le_rfl hy, Category.id_comp, Category.id_comp, Category.id_comp,
      gs_mul _ _ _ hy, gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) ⟨hi, hj⟩,
      gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) hy] at e
    refine e.trans ?_
    ring) hc
  obtain ⟨s, hs⟩ := exists_down ((isGen_iff u).1 hu) hL P.isLB t ht
  have w1 : w = 1 := P.ktriv (DualNumber K) _ w fun p =>
    ⟨⊤, trivial, gen_chartPull (chartPullPull (Out.translDiff P.A P.L w) _ _ rfl) s hs⟩
  have h0 : IsLieComb 0 v w := by
    have := a₃ 0 Fin.elim0 Fin.elim0 Fin.elim0 w (fun i => i.elim0) ⟨Fin.elim0, fun i => i.elim0, by rw [w1]; rfl⟩
    simpa using this
  exact (hv.2 w tw).unique hw h0

end GlobalTheory.KS.DlogPol
end
end

