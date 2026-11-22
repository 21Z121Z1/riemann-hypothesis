import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionTotal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem globalFns : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)

def toBK : DegPre.BF D F ⟶ DegPre.BF D F' := lift (fst _ _ ≫ θ) (snd _ _)

theorem toBK_fst : toBK θ D ≫ fst _ _ = fst _ _ ≫ θ := lift_fst _ _

theorem toBK_prB : toBK θ D ≫ DegPre.prB D F' = DegPre.prB D F := lift_snd _ _

theorem famφ_eq (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by
  have e₀ := toBK_prB θ D
  have e₂ := comp_cP D (toBK θ D) α
  fin_cases i
  · exact congrArg (fun q => q.left) e₀.symm
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul (toBK θ D) (DegPre.prB D _) (cP D _ α)).trans
      (congrArg₂ (· * ·) e₀ e₂)).symm
  · exact congrArg (fun q => q.left) e₂.symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toBK θ D)).symm

theorem trF_toBK (mu : D.X) :
    DegPre.trF D F mu ≫ toBK θ D = toBK θ D ≫ DegPre.trF D F' mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, toBK_fst, Category.assoc, trF_eq, trF_eq, tr_fst, toBK_fst, ← Category.assoc, tr_fst]
  · refine (Category.assoc _ _ _).trans ((congrArg _ (toBK_prB θ D)).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))
    rw [trF_eq, trF_eq, tr_pr]
    refine Eq.trans ?_ (congrArg (toBK θ D ≫ ·) (tr_pr D F' (cP D _ mu))).symm
    rw [MonObj.comp_mul, toBK_prB, comp_cP, comp_cP, comp_cP]

theorem exists_famPull (hθ : θ.left ≫ jFK (R := R) F' = jFK (R := R) F) (k : ℕ) (S : Fam D F' k) : ∃ S' : Fam D F k,
    ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (S'.s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := by
  have hp : (toBK θ D).left ≫ (DegPre.BF D F').hom =
      (DegPre.BF D F).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Over.w _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))
  let s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) := fun α =>
    pullOver D.P.L (DegPre.famε k) hp (famφ_eq θ D α) (S.s α)
  have hs : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := fun α Z r z J hJ =>
    sval_pullOver hp (famφ_eq θ D α) (S.s α) r hJ
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩, hs⟩
  have e₁ := (gen_fe globalFns k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F') globalFns k mu α
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (S.fe mu α u' hu' hc') _ (toBK θ D).left y J hJ
  rw [hv' u' hu' hc' _ (toBK θ D) y J hJ, ← Over.comp_left, ← trF_toBK, Over.comp_left] at e₂
  rw [Over.id_left] at e₁
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, Category.id_comp, Category.id_comp, e₂, e₁]
  have a : (toBK θ D ≫ fst _ _).left ≫ jFK (R := R) F' =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [toBK_fst, Category.id_comp, Over.comp_left, Category.assoc, hθ]
  rw [val_famMult _ hJ, val_famMult _ hJ, a, uVal, uVal, toBK_prB, comp_cP, comp_cP, comp_cP, comp_cP,
    Category.id_comp (DegPre.prB D F)]

omit [Algebra (FractionRing R) F] in

theorem secLin_of_secScal {X Y Y' W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₀ K K₁ : Type} [Fintype K₀] [Fintype K]
    [Fintype K₁] {φ₀ : K₀ → (W ⟶ X)} {ε₀ : K₀ → ℤ} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ₁ : K₁ → (Y' ⟶ X)}
    {ε₁ : K₁ → ℤ} {h : Y ⟶ W} (p : Y' ⟶ Y) {h' : Y' ⟶ W} (hh : h' = p ≫ h) {ρ : Y ⟶ Spec (CommRingCat.of R)}
    {π : Y' ⟶ Spec (CommRingCat.of F)} (g : R →+* F) (hπ : p ≫ ρ = π ≫ Spec.map (CommRingCat.ofHom g)) {n : ℕ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {v : Fin n → LB.Sec (LB.LinComb L φ ε)}
    {σ : Fin n → LB.Sec (LB.LinComb L φ₀ ε₀)} {c d : Fin n → F} {r : Fin n → R} (hd : ∀ i, d i * g (r i) = c i)
    (hσ : ∀ i, GeneratorPullback.SecScal L φ ε (v i) φ₀ ε₀ (σ i) h (scal ρ (r i)))
    (hs : ∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = ∑ i, constVal (𝟙 Y' ≫ π) y (c i) * sval (v i) (𝟙 Y' ≫ p) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₀ ε₀ σ h' (fun i => scal π (d i)) := by
  subst hh
  refine (secLin_iff_val hL s₁ σ _ _).2 fun y J hJ => (hs y J hJ).trans (Finset.sum_congr rfl fun i _ => ?_)
  have key : ∀ q : Y' ⟶ Y, sval (σ i) (q ≫ h) y J = gs q y ⊤ (scal ρ (r i)) * sval (v i) q y J := fun q => by
    rw [sval_of (σ i) (q ≫ h) y J (fun k => J (q ≫ h ≫ φ₀ k)) (fun k => by rw [Category.assoc])]
    have hm : q y ∈ LB.wchart L φ (fun k => J (q ≫ φ k)) ⊓
        LB.wchart L (fun k => h ≫ φ₀ k) (fun k => J (q ≫ h ≫ φ₀ k)) :=
      ⟨hJ.mem φ q, hJ.mem (fun k => h ≫ φ₀ k) q⟩
    have e := congrArg (gs q y _) (hσ i (fun k => J (q ≫ φ k)) (fun k => J (q ≫ h ≫ φ₀ k)) (by
      rintro (a | a) (b | b) e <;> exact congrArg (fun t => J (q ≫ t)) e))
    exact ((gs_res q y _ hm _).trans (gs_pull q h y (LB.wchart L φ₀ (fun k => J (q ≫ h ≫ φ₀ k)))
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
      (e.trans ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res q y le_top hm _) (gs_res q y _ hm _))))
  rw [← Category.assoc, key, gs_scal, gs_scal, Category.assoc, hπ, ← Category.assoc, constVal_specMap,
    ← _root_.mul_assoc, ← hd i]
  congr 1
  exact (congrArg (gs _ y ⊤) (map_mul _ _ _)).trans (gs_mul _ y ⊤ trivial _ _)

omit [Algebra (FractionRing R) F'] in
theorem sval_fam_sum {k n : ℕ} (c : Fin n → F) (s : Fin n → Fam D F k) (α : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval ((∑ i, c i • s i).s α) r z J =
      ∑ i, constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z (c i) * sval ((s i).s α) r z J := by
  classical
  generalize (Finset.univ : Finset (Fin n)) = S
  induction S using Finset.induction_on with
  | empty => exact gs_zero' r z _ (hJ.mem _ r)
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sval_add _ _ _ _ z hJ, ih,
      sval_smul _ _ _ _ z hJ]; rfl

variable (F) in
theorem exists_toFrac : ∃ θ : TF (R := R) F ⟶ TF (R := R) (FractionRing R),
    θ.left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) F := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫ jFK (R := R) (FractionRing R) =
    jFK (R := R) F := (Spec.map_comp _ _).symm
  exact ⟨Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) h)), h⟩

theorem exists_expandsF (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (hk : 1 ≤ k) (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  have e₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  obtain ⟨σ', hσ'⟩ := exists_move A.isLB U.LG.isLB hw
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k : ℤ) (U.genF F).left e₁
    (g₂ := UnifPre.gFK (G := G) F) rfl t
  have H : IsPullback (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
      (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (pullback.snd G.hom (jK R))
      (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))) :=
    (IsPullback.of_hasPullback _ _).flip
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := by
    have := A.isAb.proper
    have : IsIso U.gen.hom.left := ((Over.forget _).mapIso U.gen).isIso_hom
    have : IsLocallyNoetherian ((Over.pullback (jK R)).obj G).left :=
      LocallyOfFiniteType.isLocallyNoetherian (U.gen.hom.left ≫ A.A.hom)
    have : CompactSpace ((Over.pullback (jK R)).obj G).left :=
      QuasiCompact.compactSpace_of_compactSpace (U.gen.hom.left ≫ A.A.hom)
    have : IsNoetherian ((Over.pullback (jK R)).obj G).left := {}
    infer_instance
  obtain ⟨n, c, v, hv⟩ := (isExtension_pullOver H U.LG.isLB (I := Fin 1)
    (φ := fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))
    (φ' := fun _ => UnifPre.gFK (G := G) F) (fun _ => rfl)).exists_sum σ'
  choose S hS using fun i => ((U.expand k hk).1 (v i)).exists
  choose r hr σ f hσ hf he using hS
  obtain ⟨θ, hθ⟩ := exists_toFrac (R := R) F
  choose S' hS' using fun i => exists_famPull θ D.toPre hθ k (S i)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hg : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom g) := (Spec.map_comp _ _).symm
  have hd : ∀ i, c i * (g (r i))⁻¹ * g (r i) = c i := fun i => inv_mul_cancel_right₀
    ((map_ne_zero_iff g ((algebraMap (FractionRing R) F).injective.comp
      (IsFractionRing.injective R (FractionRing R)))).2 (hr i)) _
  refine ⟨∑ i, c i • S' i, σ', (isoRelM_iff w _ k _ e₁ _ (Category.id_comp _) t σ').2 fun y i₂ i₁ a₂ a₁ => ?_,
    n, fun i => c i * (g (r i))⁻¹, σ, f, he, ?_, fun α => ?_⟩
  · rw [Category.comp_id]
    exact hσ' _ (𝟙 _) y i₂ i₁ a₂ a₁
  · refine secLin_of_secScal U.LG.isLB (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left rfl g
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) H.w).trans
        ((Category.assoc _ _ _).trans (congrArg _ hg)))) hd hσ fun y J hJ => ?_
    refine (congrArg (fun x => sval x _ y J) hv).trans ((sval_sum' hJ _ _ _).trans
      (Finset.sum_congr rfl fun i _ => (sval_smul' hJ _ _ _).trans (congrArg _ ?_)))
    exact sval_pullOver H.w (fun _ => rfl) (v i) _ hJ
  · refine secLin_of_secScal D.toPre.P.isLB (toBK θ D.toPre).left
      (congrArg (fun q => q.left) (toBK_prB θ D.toPre)).symm g
      ((Over.w _).trans ((Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm.trans (congrArg _ hg))) hd
      (fun i => hf i α) fun y J hJ => ?_
    refine (sval_fam_sum D.toPre c S' α _ y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
    exact hS' i α _ _ y J hJ

theorem main : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s :=
  fun _ => exists_expandsF

end GlobalTheory.ExpansionTotal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfFaithfullyFlatBase
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem levelff_stalkMap_injective {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  have hl : IsLocalHom (f.stalkMap x).hom := inferInstance
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem levelff_gs_comp {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (p z) ∈ U)
    (a : Γ(X, U)) : gs (p ≫ r) z U a = (p.stalkMap z).hom (gs r (p z) U a) := by
  rw [← gs_pull p r z U h, gs_eq p z (r ⁻¹ᵁ U) h, gs_eq r (p z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply p (r ⁻¹ᵁ U) z h _).symm

theorem sval_eq_zero_of_faithfullyFlat_base : ∀ (R W : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W] (I : Ideal R) (e : ℕ) (Y : Over (Spec (CommRingCat.of R))) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (ω : Z ⟶ Spec (CommRingCat.of W)), ω ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = r ≫ Y.hom → (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R W _ _ _ _ I e Y X L hL K _ φ ε d H Z r hρ z J hJ
  let g : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R W))
  have hg : Flat g ∧ Surjective g := by
    refine (flat_and_surjective_SpecMap_iff _).2 ?_
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  obtain ⟨_, _⟩ := hg
  let p : pullback (r ≫ Y.hom) g ⟶ Z := pullback.fst _ _
  have : Flat p := inferInstance
  have : Surjective p := inferInstance
  obtain ⟨z', rfl⟩ := p.surjective z
  obtain ⟨ρ, hρ⟩ := hρ
  choose J' hJ' using fun χ : pullback (r ≫ Y.hom) g ⟶ X => exists_chart hL (χ z')
  have h0 := H _ (p ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition.symm)
    ⟨p ≫ ρ, by rw [Category.assoc, hρ, Category.assoc]⟩ z' J' hJ'
  have hm : r (p z') ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have h1 := sec_trans d (p ≫ r) z' (j := fun k => J (r ≫ φ k)) hm (Good.mem hJ' φ (p ≫ r))
  have h2 : gs (p ≫ r) z' (LB.wchart L φ (fun k => J (r ≫ φ k))) (d.f (fun k => J (r ≫ φ k))) = 0 :=
    h1.trans ((congrArg _ h0).trans (mul_zero _))
  apply levelff_stalkMap_injective p z'
  rw [map_zero]
  exact (levelff_gs_comp p r z' _ hm _).symm.trans h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TranslationUnitMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubN_mul_cubN_add {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (k l : ℕ) (b c m y : A) :
    cubN θ k b m y * cubN θ l c m y * θ (b * m ^ k) (c * m ^ l) y = cubN θ (k + l) (b * c) m y * θ b c y := by
  induction k with
  | zero =>
    induction l with
    | zero => simp [cubN]
    | succ l ih =>
      have e := h.coc b (c * m ^ l) m y
      simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, Nat.zero_add, pow_zero, _root_.mul_one,
        _root_.one_mul] at ih ⊢
      rw [pow_succ m, ← _root_.mul_assoc c, _root_.mul_assoc b c]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have e' := congrArg Additive.ofMul e
      simp only [_root_.mul_assoc b c] at ih'
      simp only [ofMul_mul, _root_.mul_assoc b c] at ih' e' ⊢
      linear_combination (norm := abel) ih' - e'
  | succ k ih =>
    have e := h.coc m (b * m ^ k) (c * m ^ l) y
    have p₁ : m * (b * m ^ k) = b * m ^ (k + 1) := by rw [pow_succ, mul_comm m, _root_.mul_assoc]
    have p₂ : b * m ^ k * (c * m ^ l) = b * c * m ^ (k + l) := by rw [pow_add, _root_.mul_mul_mul_comm]
    rw [p₁, p₂, h.s01 m, h.s01 m] at e
    rw [Nat.add_right_comm]
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at ih' e' ⊢
    linear_combination (norm := abel) ih' + e'

theorem translationUnit_mul :
    ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (k l : ℕ) (b c m y : A), (cubN θ k b m y * (θ b y m)⁻¹) * (cubN θ l c m y * (θ c y m)⁻¹) * θ (b * m ^ k) (c * m ^ l) y * θ b c m = θ b c (y * m) * (cubN θ (k + l) (b * c) m y * (θ (b * c) y m)⁻¹) := by
  intro A U _ _ θ h k l b c m y
  have a := congrArg Additive.ofMul (cubN_mul_cubN_add h k l b c m y)
  have e := congrArg Additive.ofMul (h.compat b c y m)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a e ⊢
  linear_combination (norm := abel) a + e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_comp_stalkMap {Y Z Z' : Scheme.{0}} (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (U : Y.Opens)
    (h : r (ρ z) ∈ U) (a : Γ(Y, U)) :
    gs (ρ ≫ r) z U a = (ρ.stalkMap z).hom (gs r (ρ z) U a) := by
  rw [← gs_pull ρ r z U h a, gs_eq r (ρ z) U h, gs_eq ρ z (r ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ U) z h _).symm

theorem values_natural : ∀ (X Y Z Z' : Scheme.{0}) (L : LB X) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) ∧ (∀ s : LB.Sec (LB.LinComb L φ ε), sval s (ρ ≫ r) z J = (ρ.stalkMap z).hom (sval s r (ρ z) (fun ψ => J (ρ ≫ ψ)))) ∧ (∀ t : LB.Gen (LB.LinComb L φ ε), (val t (ρ ≫ r) z J).val = (ρ.stalkMap z).hom (val t r (ρ z) (fun ψ => J (ρ ≫ ψ))).val) ∧ ∀ c : Γ(Y, ⊤), gs (ρ ≫ r) z ⊤ c = (ρ.stalkMap z).hom (gs r (ρ z) ⊤ c) := by
  intro X Y Z Z' L K _ φ ε r ρ z J hJ
  have hJ' : Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) := fun ψ => hJ (ρ ≫ ψ)
  have hm := hJ'.mem φ r
  refine ⟨hJ', fun s => ?_, fun t => ?_, fun c => gs_comp_stalkMap r ρ z ⊤ trivial c⟩
  · rw [sval_of s (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact gs_comp_stalkMap r ρ z _ hm _
  · rw [val_of t (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact (gs_unit (ρ ≫ r) z _ hm _).symm.trans ((gs_comp_stalkMap r ρ z _ hm _).trans
      (congrArg (ρ.stalkMap z).hom (gs_unit r (ρ z) _ hm _)))

end GlobalTheory
end

