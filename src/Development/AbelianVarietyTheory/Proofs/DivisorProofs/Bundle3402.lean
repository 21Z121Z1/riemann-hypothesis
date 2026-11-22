import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightPullbackPointTranslation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTransWt

theorem valR_pbT_le {A : Type} [CommRing A] {X Z : Scheme.{0}} (w : Sp A ⟶ Z) (T : Z ⟶ X) {U : X.Opens}
    {U' : Z.Opens} (hU : U' ≤ T ⁻¹ᵁ U) (h : ⊤ ≤ w ⁻¹ᵁ U') (f : Γ(X, U)) :
    valR w U' (pbT T f U') = valR (w ≫ T) U f := by
  have h' : ⊤ ≤ (w ≫ T) ⁻¹ᵁ U := h.trans (w.preimage_mono hU)
  unfold valR
  rw [dif_pos h, dif_pos h', GlobalTheory.KS.pbT_of_le T hU]
  rw [← Scheme.Hom.appLE_comp_appLE w T U U' ⊤ hU h]
  rfl

theorem isWt_pbT_tr : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (α : Q.X) (U U' : Y.H.left.Opens), U' ≤ GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U → ∀ f : Γ(Y.H.left, U), IsWt Y α U f → IsWt Y α U' (pbT (GlobalTheory.HeatTrans.tr Y.H x) f U') := by
  intro R _ _ Q O _ _ _ oa Y x α U U' hU f hf S _ φ x₁ x₁' c a a' ha ha' hV hV' hq hc
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let z : Over.mk (spMap φ) ⟶ Y.H := toUnit _ ≫ x
  have hleft : ∀ w : Over.mk (spMap φ) ⟶ Y.H, (w * z).left = w.left ≫ GlobalTheory.HeatTrans.tr Y.H x := fun w => by
    have e : w ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)) = w * z := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (w ≫ toUnit Y.H) (toUnit _)]
    rw [← e]; rfl
  rw [valR_pbT_le a' _ hU hV', valR_pbT_le a _ hU hV]
  subst ha ha'
  rw [← hleft, ← hleft]
  refine hf S φ (x₁ * z) (x₁' * z) c _ _ rfl rfl ?_ ?_ ?_ ?_
  · rw [hleft]; exact hV.trans (x₁.left.preimage_mono hU)
  · rw [hleft]; exact hV'.trans (x₁'.left.preimage_mono hU)
  · rw [MonObj.mul_comp, MonObj.mul_comp, hq]
  · intro χ y J hJ
    have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ z)).2 χ y J hJ
    have h1' := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' z)).2 χ y J hJ
    simp only [Y.Φ_b, GlobalTheory.TorusModel.cv] at h1 h1'
    rw [hq] at h1'
    refine mul_right_cancel (h1'.trans ?_)
    rw [hc χ y J hJ, _root_.mul_assoc, ← h1, _root_.mul_assoc]

end GlobalTheory.HeatTransWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixTransposeEqAtPolarizedPoint
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

open GlobalTheory.KS GlobalTheory.KS.Sym

noncomputable section

namespace GlobalTheory.FibSym

def chartPullComp {X X' Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ X') :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h :=
  have hm : ∀ (y : Y') (J : PUnit → L.ι), y ∈ (L.pull (h ≫ F)).U J → h y ∈ (L.pull F).U J := fun y J hy =>
    (mem_pull (L := L) (F := F) (x := h y) (J := J)).2 ((mem_pull (L := L) (F := h ≫ F) (x := y) (J := J)).1 hy)
  { idx := fun J => J
    le := fun J y hy => hm y J hy
    g := fun y J J' hj hj' => (gm_pull_g L (h ≫ F) (𝟙 _) y J J' hj hj').trans
      (by rw [Category.id_comp]; exact (gm_pull_g L F h y J J' (hm y J hj) (hm y J' hj')).symm) }

theorem square_fibre_affine_opens_grp (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R]
    (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G] [IsSeparated G.hom] (m : P₀.A.left ⟶ G.left)
    (h : IsGrpPullback P₀.A G (spMap x₀) m) :
    (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (G ⊗ G).left, IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧
    IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧
    (∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧
    ∀ W W' : G.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from G.left) := by
      rw [← terminal.comp_from G.hom]; infer_instance
    exact hW.inf hW'

theorem exists_symm_of_ksCoc_grp (l₁ : Out.Laws) (l₂ : Out.Laws2)
    (hT : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A))
    (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hv : IsLieBasis v)
    (hdd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G]
    [IsSeparated G.hom] (m : P₀.A.left ⟶ G.left) (L : LB G.left) [Finite L.ι] (D : R → K)
    (d : L.ι → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i))
    (hpb : IsGrpPullback P₀.A G (spMap x₀) m) (hL : L.IsLB) (haff : ∀ i, IsAffineOpen (L.U i))
    (hiso : LBIso P₀.L (L.pull m)) (hks : KSCoc P₀.A.hom G.hom m D L.U dd d θ) (hφ : IsDlog m L dd φ) :
    ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ) := by
  obtain ⟨⟨m₂, hsq, sq₀, sqb⟩, hsep, hpull, hpre, hinf⟩ := square_fibre_affine_opens_grp K P₀ R x₀ G m hpb
  obtain ⟨hc, hind⟩ := (GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd _ m L hL hiso).2 φ hφ
  have hm : m ≫ G.hom = P₀.A.hom ≫ spMap x₀ := hpb.1.w
  have prod := fun W W' hW hW' => GlobalTheory.KS.ProdLift.main K R x₀ G P₀.A m m₂ D W W' hm hsq hW hW' _ rfl
  choose d₂ hd₂ c₁ c₂ using fun i j => (prod _ _ (haff i) (haff j)).1 (d i) (d j) (hks.der i) (hks.der j)
  choose w a₁ a₂ a₃ a₄ w₀ w₁ w₂ using fun a =>
    GlobalTheory.KS.SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a) _ _ (Or.inl ⟨rfl, rfl⟩)
  choose w' b₁ b₂ b₃ b₄ w₀' w₂' w₁' using fun a =>
    GlobalTheory.KS.SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a) _ _ (Or.inr ⟨rfl, rfl⟩)
  have hw : ∀ a, IsVF _ (w a) := fun a => ⟨a₁ a, a₂ a, a₃ a, a₄ a⟩
  have hw' : ∀ a, IsVF _ (w' a) := fun a => ⟨b₁ a, b₂ a, b₃ a, b₄ a⟩
  have cov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := top_le_iff.1
    ((le_iSup_inf_preimage m L.U hL.cover ⊤).trans (iSup_mono fun _ => inf_le_right))
  obtain ⟨k, e, e', h₁, h₂, h₃, h₄, h₅⟩ := exists_square_data (θ := θ) sq₀ hsq.1 hsq.2 hL hd₂ hφ hc hw hw' w₀ w₁ w₂ w₀' w₂' w₁'
    (fun i i' j O hO f => diff_prod x₀ (hks.der i) (hks.der i') (hks.der j) (haff i) (haff i') (haff j) sqb
      (hd₂ i j) (hd₂ i' j) hsq.1 hsq.2 inf_le_left inf_le_left inf_le_right inf_le_right
      (fun x hx => by exact ⟨hx.1.1, hx.2⟩) (fun x hx => by exact ⟨hx.1.2, hx.2⟩) (c₁ i j) (c₂ i j) (c₁ i' j) (c₂ i' j)
      (prod _ _ (hinf _ _ (haff i) (haff i')) (haff j)).2 (fun a => θ a i i') (hks.diff i i' _ le_rfl) hw w₁ w₂ O hO f)
    (fun i j j' O hO f => diff_prod x₀ (hks.der j) (hks.der j') (hks.der i) (haff j) (haff j') (haff i) sqb
      (hd₂ i j) (hd₂ i j') hsq.2 hsq.1 inf_le_right inf_le_right inf_le_left inf_le_left
      (fun x hx => by exact ⟨hx.1, hx.2.1⟩) (fun x hx => by exact ⟨hx.1, hx.2.2⟩) (c₂ i j) (c₁ i j) (c₂ i j') (c₁ i j')
      (fun a b ha hb u u' => (prod _ _ (haff i) (hinf _ _ (haff j) (haff j'))).2 a b ha hb u' u)
      (fun a => θ a j j') (hks.diff j j' _ le_rfl) hw' w₂' w₁' O hO f)
    _ (fun _ => le_rfl) (fun a => GlobalTheory.KS.Primitive.cech_primitive l₁ l₂ hT K P₀ _ _ (φ a) cov (hc a))
  refine GlobalTheory.KS.exists_isSymm_of_square K _ _ P₀.A.hom _ _ L.ι _ g θ φ hsep hpull (fun i => hpre _ (haff i)) hind _ _ k e e' ?_
    h₁ h₂ h₃ h₄ h₅
  refine top_le_iff.1 fun x _ => ?_
  have pt : ∀ y : P₀.A.left, ∃ i, y ∈ m ⁻¹ᵁ L.U i := fun y =>
    TopologicalSpace.Opens.mem_iSup.1 (cov.ge trivial)
  obtain ⟨i, hi⟩ := pt ((fst P₀.A P₀.A * snd P₀.A P₀.A).left x)
  obtain ⟨j, hj⟩ := pt ((fst P₀.A P₀.A).left x)
  obtain ⟨l, hl⟩ := pt ((snd P₀.A P₀.A).left x)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, l), ⟨hi, hj⟩, hl⟩

open GlobalTheory.LogKSBal in

theorem map_transpose_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (x₀ : Γ(X, U.1) →+* K) (P₀ : Out.PolAV (Sp K)) (mm : P₀.A.left ⟶ t.G.left), IsGrpPullback P₀.A t.G (spMap x₀ ≫ chart U) mm → LBIso P₀.L (t.PP.L.pull mm) → U.1 ≤ V → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → (Θ.map x₀)ᵀ = Θ.map x₀ := by
  intro E _ _ _ H X t V U n v hv hb K _ _ x₀ P₀ mm hpq hPL hUV D Θ hKS
  letI : GrpObj ((Over.pullback (chart U)).obj t.G) := Functor.grpObjObj
  let G := (Over.pullback (chart U)).obj t.G
  have hs := IsSemiAbelian.pullback (chart U) t.G t.semi
  have : IsSeparated G.hom := hs.separated
  have : QuasiCompact G.hom := hs.quasiCompact
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := P₀.isAb.comm
  let io : G.left ⟶ t.G.left := pullback.fst t.G.hom (chart U)
  have hpb : IsGrpPullback G t.G (chart U) io := isGrpPullback_pullback t.G (chart U)
  have hw : mm ≫ t.G.hom = (P₀.A.hom ≫ spMap x₀) ≫ chart U := by
    rw [hpq.1.w, Category.assoc]
  let m : P₀.A.left ⟶ G.left := pullback.lift mm (P₀.A.hom ≫ spMap x₀) hw
  have hmio : m ≫ io = mm := pullback.lift_fst _ _ _
  have hmG : m ≫ G.hom = P₀.A.hom ≫ spMap x₀ := pullback.lift_snd _ _ _
  rw [← hmio] at hpq hPL
  have hm : IsGrpPullback P₀.A G (spMap x₀) m := IsGrpPullback.cancel hpb hpq hmG
  obtain ⟨b₁, b₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t x₀ _ n v hv hb
  obtain ⟨u, hu, hbas, -⟩ := exists_lieBasis t hpq _ b₁ b₂
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hbas.1 a)).1
  obtain ⟨L, hfin, hL, haff, hiso, d, hd⟩ := exists_ksCoc t hUV hKS hpb.1 x₀ hpq hbas.1 hu hdd
  have hI : LBIso P₀.L (L.pull m) := LBIso.trans P₀.isLB (pull_isLB t.PP.isLB _) (pull_isLB hL _) hPL
    (hiso.chartPull (chartPullComp t.PP.L io m) (Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hbas hdd _ _ L hL hI
  obtain ⟨Θ', hs', hΘ'⟩ := exists_symm_of_ksCoc_grp GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.T.theorem_of_cube_polAbelianScheme K P₀ n u dd hbas hdd _ x₀ G m L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e : Θ' = -Θ.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [lc_sub]
    exact hΘ' b
  have h : Θ'ᵀ = Θ' := hs'
  rwa [e, Matrix.transpose_neg, neg_inj] at h

end GlobalTheory.FibSym

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPoint
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

namespace GlobalTheory.KSPtUniq

theorem isKS_unique_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (φ : Γ(X, U.1) →+* K) (P₀ : PolAV (Sp K)) (m : P₀.A.left ⟶ t.G.left), ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ V → IsGrpPullback P₀.A t.G (spMap φ ≫ chart U) m → LBIso P₀.L (t.PP.L.pull m) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → IsKS t V U v D Θ' → φ.mapMatrix Θ = φ.mapMatrix Θ' := by
  intro E _ _ _ H X t V U n v hv hb K _ _ φ P₀ m hV hpb hiso D Θ Θ' hK hK'
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  set x0 : Sp K ⟶ X := spMap φ ≫ chart U with hx0def
  have hUx : ⊤ ≤ x0 ⁻¹ᵁ U.1 := fun o _ => by
    show (chart U) ((spMap φ) o) ∈ (U.1 : Set X)
    rw [← U.2.range_fromSpec]
    exact ⟨_, rfl⟩
  have hev : GlobalTheory.FlagMod.ev x0 U.1 hUx = φ := GlobalTheory.FlagMod.ev_spMap_tau U.2 φ hUx
  have hx : spMap (GlobalTheory.FlagMod.ev x0 U.1 hUx) ≫ chart U = x0 := by rw [hev]
  have hv' := fun i => GlobalTheory.LieMet.isTan_map (GlobalTheory.FlagMod.ev x0 U.1 hUx) hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map (GlobalTheory.FlagMod.ev x0 U.1 hUx) hx hv hb
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.LiePull.lieBasis_of_tanBasis t x0 P₀.A m hpb _ hv' hb'
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hu.1 a)).1
  obtain ⟨⟨φc, hφc⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd _ m t.PP.L t.PP.isLB hiso
  obtain ⟨J, W, j, d, hcov, hWj, hf, hl, hdiff⟩ := hK
  obtain ⟨J', W', j', d', hcov', hWj', hf', hl', hdiff'⟩ := hK'
  have hP := GlobalTheory.KSUniq.pull_diff t V U v hv Θ W j d hWj hdiff x0 hUx P₀.A m hpb u hu' dd hdd φc hφc
  have hP' := GlobalTheory.KSUniq.pull_diff t V U v hv Θ' W' j' d' hWj' hdiff' x0 hUx P₀.A m hpb u hu' dd hdd φc hφc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W i) hp
    exact this.1
  have hWU' : ∀ i, W' i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov' ▸ (le_iSup W' i) hp
    exact this.1
  have hfib : ∀ z, t.G.hom (m z) ∈ U.1 ⊓ V := fun z => by
    rw [← Scheme.Hom.comp_apply, hpb.1.w, Scheme.Hom.comp_apply]
    exact ⟨hUx (Set.mem_univ _), hV (Set.mem_univ _)⟩
  have hcv : ∀ z, ∃ i, m z ∈ W i := fun z => by
    have h2 : m z ∈ ⨆ i, W i := by rw [hcov]; exact hfib z
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have hcv' : ∀ z, ∃ i, m z ∈ W' i := fun z => by
    have h2 : m z ∈ ⨆ i, W' i := by rw [hcov']; exact hfib z
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have := GlobalTheory.KSUniq.theta_eq_fibre P₀ u hu dd hdd t.G.hom x0 m hpb.1 U.2 t.PP.L t.PP.isLB hiso _
    (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hUx (Θ a b))
    (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hUx (Θ' a b))
    W W' j j' d d' hWU hWU' hWj hWj' hcv hcv' hf hf' hl hl' φc hφc hP hP'
  rw [hev] at this
  ext a b
  exact congrFun (congrFun this a) b

end GlobalTheory.KSPtUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoCubeOfGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.Mum.EFixCube

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cube_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J →
    ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre J D A G), IsSemiAbelian G → ∀ (x y x' y' : G ⟶ G) (cx cy cx' cy' : A.A ⟶ A.A),
    Gen₀ U U x cx → Gen₀ U U y cy → Gen₀ U U x' cx' → Gen₀ U U y' cy' →
    LBIso (cubeLB A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] A.L) (cubeLB A.A ![fst A.A A.A ≫ cx', snd A.A A.A ≫ cy'] A.L) →
    LBIso (cubeLB G ![fst G G ≫ x, snd G G ≫ y] U.LG.L) (cubeLB G ![fst G G ≫ x', snd G G ≫ y'] U.LG.L) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ hS x₁ y₁ x₂ y₂ cx₁ cy₁ cx₂ cy₂ hx₁ hy₁ hx₂ hy₂ hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ (x y : G₁ ⟶ G₁) (cx cy : A₁.A ⟶ A₁.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G₁ ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U₁.LG.L U₁.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A₁.L A₁.isLB))) := by
    intro x y cx cy hx hy
    have hL := U₁.LG.isLB
    have hA := A₁.isLB
    have hgen := U₁.gen_hom
    have hc' : CechPic.pull (pullback.fst G₁.hom (jK R)) (cls U₁.LG.L hL) =
        CechPic.pull U₁.gen.hom.left (cls A₁.L hA) := by
      obtain ⟨w, hw⟩ := U₁.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G₁ (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hA₁ := A₁.isLB
  have l₁ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₁, snd G₁ G₁ ≫ y₁] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have l₂ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₂, snd G₁ G₁ ≫ y₂] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have m₁ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have m₂ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] (cls _ hA₁) =
      cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] (cls _ hA₁) :=
    (cls_cubeLB _ _ hA₁).symm.trans (((cls_eq_iff m₁ m₂).2 hA).trans (cls_cubeLB _ _ hA₁))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ l₁ l₂ ?_
  refine (cls_eq_iff (pull_isLB l₁ _) (pull_isLB l₂ _)).1 ?_
  rw [cls_pull l₁ _ (pull_isLB l₁ _), cls_pull l₂ _ (pull_isLB l₂ _), cls_cubeLB _ _ hL₁, cls_cubeLB _ _ hL₁,
    key x₁ y₁ cx₁ cy₁ hx₁ hy₁, key x₂ y₂ cx₂ cy₂ hx₂ hy₂, eA]

theorem cube_adj_of_oLinear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G), IsSemiAbelian G → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → ∀ a : O,
    LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ U hS O _ _ _ ιD ιA ιG hl a
  have g₁ : Gen₀ U U (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hA := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local (FractionRing R) A.A A.L (ιA.act a) (ιA.act (star a)) A.isLB (ιA.rosati a)
  have := lbIso_cube_of_generic R _ hR D A G U hS (ιG.act a) (𝟙 G) (𝟙 G) (ιG.act (star a)) (ιA.act a) (𝟙 A.A) (𝟙 A.A)
    (ιA.act (star a)) (hl.ext a) g₁ g₁ (hl.ext (star a)) (by simpa only [Category.comp_id] using hA)
  simpa only [Category.comp_id] using this

end GlobalTheory.Mum.EFixCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VertSpanZero

theorem le_preimage_of_closedPoint {Z : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Z)
    (V : Z.Opens) (h : y.base (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro p _
  exact ((IsLocalRing.specializes_closedPoint p).map y.continuous).mem_open V.isOpen h

theorem snd_valR_epsMul {Z : Scheme.{0}} {S : Type} [CommRing S] (T : Sp (DualNumber S) ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ T ⁻¹ᵁ O) (a : S) (f : Γ(Z, O)) :
    (valR (spMap (epsMul a) ≫ T) O f).snd = a * (valR T O f).snd := by
  rw [GlobalTheory.Points.valR_spMap_comp (epsMul a) T O h f]
  simp [epsMul]

theorem epsMul_comp_algebraMap {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_epsMul {S : Type} [CommRing S] (a : S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul a) = (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul]

theorem epsMul_zero' {S : Type} [CommRing S] :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.VertSpanZero

namespace GlobalTheory.VertSpanZero

theorem spMap_fst_algebraMap (S : Type) [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

def redOver {X : Scheme.{0}} {S : Type} [CommRing S] (x : Sp S ⟶ X) : Over.mk x ⟶ tEpsG x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ x = x
    rw [← Category.assoc, spMap_fst_algebraMap, Category.id_comp])

theorem redOver_comp_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (x : Sp S ⟶ X)
    (l : List (tEpsG x ⟶ G)) (hl : ∀ u ∈ l, redOver x ≫ u = 1) : redOver x ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl u List.mem_cons_self,
      ih fun u' h => hl u' (List.mem_cons_of_mem _ h), _root_.mul_one]

theorem red_mul_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G) (hg' : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g) {n : ℕ}
    (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G))
    (hu : ∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (g' * (List.ofFn u).prod).left = g := by
  have h1 : redOver (g ≫ G.hom) ≫ (List.ofFn u).prod = 1 := by
    refine redOver_comp_prod _ _ fun w hw => ?_
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' u w).1 hw
    exact Over.OverMorphism.ext (hu a)
  change (redOver (g ≫ G.hom) ≫ (g' * (List.ofFn u).prod)).left = g
  rw [MonObj.comp_mul, h1, _root_.mul_one]
  change spMap _ ≫ g'.left = g
  rw [hg', ← Category.assoc, spMap_fst_algebraMap, Category.id_comp]

end GlobalTheory.VertSpanZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealElementPullbackClosedFibreZero
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreScalar

theorem appLE_eq_of_eq {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) (U : Y.Opens) (W : A.Opens)
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

theorem fromSpec_appLE_top {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(Y, U)).hom = 𝟙 _ := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem specMap_appLE_top {A B : CommRingCat.{0}} (f : A ⟶ B) (e : (⊤ : (Spec B).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ f := by
  rw [← Scheme.ΓSpecIso_naturality]
  rfl

theorem spMap_chart_appLE_top {X : Scheme.{0}} (U : X.affineOpens) (m : Ideal Γ(X, U.1))
    (e : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1) :
    (spMap (Ideal.Quotient.mk m) ≫ chart U).appLE U.1 ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk m) := by
  have e1 : (⊤ : (Sp Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have e2 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤ := le_top
  have hk := fromSpec_appLE_top U.2 e1
  change (spMap (Ideal.Quotient.mk m) ≫ U.2.fromSpec).appLE U.1 ⊤ e ≫ _ = _
  have hk' : U.2.fromSpec.appLE U.1 ⊤ e1 ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U.1))).hom = 𝟙 _ := hk
  rw [← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) U.2.fromSpec _ ⊤ _ e1 e2, Category.assoc,
    specMap_appLE_top, ← Category.assoc, hk', Category.id_comp]

theorem fibre_scalar_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O) (r : Γ(X, U.1)), r ∈ m → (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom r) = 0 := by
  intro E _ _ _ H X t U m A _ ι hpb O hO O' hO' r hr
  set g := spMap (Ideal.Quotient.mk m) ≫ chart U with hg
  have hw : ι ≫ t.G.hom = A.hom ≫ g := hpb.1.w
  have e5 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ g ⁻¹ᵁ U.1 := by
    intro x _
    change g x ∈ U.1
    rw [hg, Scheme.Hom.comp_apply]
    exact U.2.fromSpec_preimage_self.ge (Set.mem_univ _)
  have hz : (g.appLE U.1 ⊤ e5).hom r = 0 := by
    have h := congrArg (fun φ => φ.hom r) (spMap_chart_appLE_top U m e5)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr hr] at h
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom).1
    exact hinj (h.trans (map_zero _).symm)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hw,
    ← Scheme.Hom.appLE_comp_appLE A.hom g U.1 ⊤ O' e5 (fun x _ => trivial), CommRingCat.comp_apply, hz, map_zero]

end GlobalTheory.FibreScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentAbsIntClosedLocalDomaiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial T)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial T)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.GmAic.main) | (exact GlobalTheory.EtC.GmAic.main) | (intros; apply GlobalTheory.EtC.GmAic.main  <;> assumption)
end

