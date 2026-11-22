import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0049
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtOrbit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_comp {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} {e : S₁ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g)
    (he : f ≫ g = e) : ∃ m : GObjMap o₁ o₃ e, m.φ = h₁.φ ≫ h₂.φ := by
  subst he
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol
      (GlobalTheory.UPel.HT.MapComp.lbIso_pull_comp h₂.pol h₁.φ₂ rfl)
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem UpperTheory.Gal.G3.pPtOrbit :
    TransComp → TransPull → TransOfMap → TransOrbit → Rigid → PtOrbit := by
  intro hC hP hM hO hRg p _ D G L R _ _ gb N' N X' X π Φ w k _ _ x y hxy
  obtain ⟨e, o, ψ, φ, tψ, rfl⟩ := w
  have hs : y ≫ X'.s = x ≫ X'.s := by rw [← e, ← Category.assoc, ← hxy, Category.assoc]
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
  obtain ⟨oy, ⟨my⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs X'.univ
  obtain ⟨ox', ⟨nx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl o
  obtain ⟨oy', ⟨ny⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs o
  refine ⟨ox, oy, mx, my, hs, ?_⟩
  obtain ⟨ψx, tx, cx⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) x rfl _ _ X'.univ o ox ox' mx nx ψ 1 tψ
  obtain ⟨ψy, ty, cy⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) y hs _ _ X'.univ o oy oy' my ny ψ 1 tψ
  obtain ⟨A, hA⟩ := exists_comp nx φ (rfl : x ≫ π = x ≫ π)
  obtain ⟨B, hB⟩ := exists_comp ny φ hxy.symm
  obtain ⟨A', hA'⟩ := exists_comp nx φ (Category.id_comp (x ≫ π)).symm
  obtain ⟨c⟩ := BaseChange.gObjMap_cancel (f := 𝟙 (Sp k)) A' B
  obtain ⟨θ', hθ', tθ'⟩ := hM p D G L R gb (Sp k) (x ≫ X'.s) N ox' oy' c
  have i1 : Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (L.KN 1).one_mem
  have a1 : AdmK L N N 1 := fun v hv => by simpa using hv
  have t₂ := hC p D G L R gb (Sp k) (x ≫ X'.s) N' N N ox ox' oy' ψx θ' 1 1 i1 a1 tx tθ'
  rw [_root_.mul_one] at t₂
  obtain ⟨u, hu, θ, tθ, hθ⟩ := hO p D G L R gb k (x ≫ X'.s) N' N ox oy oy' (ψx ≫ θ') ψy t₂ ty
  refine ⟨u, hu, θ, tθ, ?_⟩
  have hr := hRg p D R gb X.X (Sp k) X.s (x ≫ X'.s) (x ≫ π) (by rw [Category.assoc, e]) N X.univ ox'
  obtain ⟨C, hC'⟩ := exists_comp c B (Category.id_comp (x ≫ π))
  have key : c.φ ≫ ny.φ ≫ φ.φ = nx.φ ≫ φ.φ := by
    have := hr C A
    rw [hC', hB, hA] at this
    exact this
  calc Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ ≫ φ.φ
      = Over.Hom.left θ ≫ (my.φ ≫ Over.Hom.left ψ) ≫ φ.φ := by rw [Category.assoc]
    _ = Over.Hom.left (θ ≫ ψy) ≫ ny.φ ≫ φ.φ := by rw [← cy]; simp
    _ = Over.Hom.left ψx ≫ c.φ ≫ ny.φ ≫ φ.φ := by rw [hθ, Over.comp_left, hθ', Category.assoc]
    _ = Over.Hom.left ψx ≫ nx.φ ≫ φ.φ := by rw [key]
    _ = mx.φ ≫ Over.Hom.left ψ ≫ φ.φ := by rw [← Category.assoc, cx, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PQuotUniq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma twisted_kernel_forms_nonvanishing (hE : EtDesc) (k : Type) [Field k] [IsAlgClosed k] (A A₁ A₂ : Over (Sp k)) [GrpObj A]
    [GrpObj A₁] [GrpObj A₂] (hA : IsAbelianScheme A) (hA₂ : IsAbelianScheme A₂)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left]
    (hker : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp k) (a : Over.mk t ⟶ A), a ≫ ψ₁ = 1 → a ≫ ψ₂ = 1) :
    ∃ θ : A₁ ⟶ A₂, ψ₁ ≫ θ = ψ₂ := by
  haveI := hA.smooth
  haveI := hA₂.proper
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : ψ₂.left ≫ A₂.hom = ψ₁.left ≫ A₁.hom := by rw [Over.w, Over.w]
  obtain ⟨hepi, g, hg⟩ := hE ψ₁.left A₁.hom A₂.hom ψ₂.left hw (by
    intro Ω _ _ x y hxy
    have hxy' : x ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ₁, ← Category.assoc, hxy, Category.assoc]
    let X : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk x
    let Y : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk y hxy'.symm
    have h1 : X ≫ ψ₁ = Y ≫ ψ₁ := Over.OverMorphism.ext hxy
    have h2 : (X * Y⁻¹) ≫ ψ₁ = 1 := by
      have e := (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
      have e' := map_inv (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))) Y
      simp only [IsMonHom.monoidHom_apply] at e e'
      rw [e, e', h1, mul_inv_cancel]
    have h3 := hker Ω (x ≫ A.hom) (X * Y⁻¹) h2
    have e := (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
    have e' := map_inv (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))) Y
    simp only [IsMonHom.monoidHom_apply] at e e'
    rw [e, e', mul_inv_eq_one] at h3
    exact congrArg CommaMorphism.left h3)
  haveI := hepi
  refine ⟨Over.homMk g ?_, ?_⟩
  · rw [← cancel_epi ψ₁.left, ← Category.assoc, hg, hw]
  · exact Over.OverMorphism.ext hg

theorem UpperTheory.Gal.G3.pQuotUniq :
    EtDesc → QuotUniq := by
  intro hE k _ _ A A₁ A₂ _ _ _ _ _ _ hA hA₁ hA₂ ψ₁ ψ₂ h₁ h₂ f₁ e₁ s₁ f₂ e₂ s₂ hker
  obtain ⟨θ, hθ⟩ := twisted_kernel_forms_nonvanishing hE k A A₁ A₂ hA hA₂ ψ₁ ψ₂ (fun Ω _ _ t a => (hker Ω t a).1)
  obtain ⟨θ', hθ'⟩ := twisted_kernel_forms_nonvanishing hE k A A₂ A₁ hA hA₁ ψ₂ ψ₁ (fun Ω _ _ t a => (hker Ω t a).2)
  haveI : Flat ψ₁.left := inferInstance
  haveI : Flat ψ₂.left := inferInstance
  haveI : Epi ψ₁ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₁
  haveI : Epi ψ₂ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₂
  haveI : Epi (ψ₁ ⊗ₘ ψ₁) := GlobalTheory.FlatQuotient.epi_tensorHom ψ₁ ψ₁
  have i1 : θ ≫ θ' = 𝟙 _ := by
    rw [← cancel_epi ψ₁, ← Category.assoc, hθ, hθ', Category.comp_id]
  have i2 : θ' ≫ θ = 𝟙 _ := by
    rw [← cancel_epi ψ₂, ← Category.assoc, hθ', hθ, Category.comp_id]
  refine ⟨θ, ⟨θ', i1, i2⟩, ⟨?_, ?_⟩, hθ⟩
  · rw [← IsMonHom.one_hom ψ₁, Category.assoc, hθ, IsMonHom.one_hom ψ₂]
  · have h1 : (ψ₁ ⊗ₘ ψ₁) ≫ (θ ⊗ₘ θ) = ψ₂ ⊗ₘ ψ₂ := by
      rw [tensorHom_comp_tensorHom, hθ]
    rw [← cancel_epi (ψ₁ ⊗ₘ ψ₁), ← Category.assoc, ← IsMonHom.mul_hom ψ₁, Category.assoc, hθ,
      IsMonHom.mul_hom ψ₂, ← Category.assoc, h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt)
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.CechPic GlobalTheory.AmpleRigid
open scoped TensorProduct CategoryTheory.Obj
universe u

private theorem diag_fst {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_fst]
  rfl

private theorem diag_snd {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_snd]
  rfl

section

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}}
  {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'} {f : S' ⟶ S}

private theorem tensor_left_hom_ext_of_fst_snd {S : Scheme.{0}} {X Y : Over S} {W : Scheme.{0}} {u v : W ⟶ (X ⊗ Y).left}
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  have hw : u ≫ (X ⊗ Y).hom = v ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, h₁, Category.assoc]
  let U : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk u
  let V : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk v hw.symm
  have hUV : U = V := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₁)
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₂)
  exact congrArg CommaMorphism.left hUV

private theorem map_diag (m : GObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply tensor_left_hom_ext_of_fst_snd
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_fst, Category.id_comp]
    rw [Category.assoc, m.sq.1, key, Category.assoc, diag_fst, Category.comp_id]
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_snd, Category.id_comp]
    rw [Category.assoc, m.sq.2, key, Category.assoc, diag_snd, Category.comp_id]

private theorem pull_diag_cls (m : GObjMap o' o f) :
    pull m.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← map_diag m, pull_comp,
    ← cls_pull o.isLB _ (pull_isLB o.isLB m.φ₂),
    (cls_eq_iff (pull_isLB o.isLB m.φ₂) o'.isLB).2 (LBIso.symm m.pol)]

private theorem eq_at_point (hN : 3 ≤ N) (m m' : GObjMap o' o f) {K : Type} [Field K] [IsAlgClosed K] (j : Sp K ⟶ S') :
    pullback.fst o'.A.hom j ≫ m.φ = pullback.fst o'.A.hom j ≫ m'.φ := by
  have hA' : IsAbelianScheme ((Over.pullback j).obj o'.A) := by
    haveI := o'.ab.comm
    haveI := o'.ab.smooth
    haveI := o'.ab.proper
    haveI := o'.ab.geomConnected
    constructor
    · infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
  have c := (isGrpPullback_pullback o'.A j).comp m.cart
  have c' := (isGrpPullback_pullback o'.A j).comp m'.cart
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample hA' c c' ?_ hN ?_ ?_
  · rw [pull_comp, pull_comp, pull_diag_cls m, pull_diag_cls m']
  · intro h0
    let ψ : ℚ →+* K := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of K) (j ≫ s')).hom.comp
      (algebraMap ℚ R)
    have e0 : ψ (N : ℚ) = ψ 0 := by rw [map_natCast, map_zero]; exact h0
    have e1 : (N : ℚ) = 0 := ψ.injective e0
    norm_cast at e1
    omega
  · intro Ω _ _ t x hx
    let β : R →+* Ω := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of Ω) ((t ≫ j) ≫ s')).hom
    have hβ : (t ≫ j) ≫ s' = spMap β := by
      simp only [spMap, β, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o'.geom Ω (t ≫ j) β hβ
    let x₁ := pushHom (isGrpPullback_pullback o'.A j) (Over.mk t) x
    have hx₁ : x₁ ^ N = 1 := by
      simp only [x₁]
      rw [← map_pow, hx, map_one]
    obtain ⟨y, hy⟩ := (I.onto N (by omega) x₁).1 hx₁
    have hl : x.left ≫ pullback.fst o'.A.hom j = x₁.left := rfl
    have key : ∀ mm : GObjMap o' o f, x.left ≫ pullback.fst o'.A.hom j ≫ mm.φ =
        (toUnit (Over.mk (t ≫ j))).left ≫ f ≫ (o.eta y).left := by
      intro mm
      rw [← Category.assoc, hl, ← hy, ← hI y, Over.comp_left, Category.assoc, mm.eta y]
    rw [key m, key m']

end

theorem UpperTheory.Gal.G3.pRigid :
    Rigid := by
  intro p _ D R _ _ gb S S' s s' f hf N o o' m m'
  have hN : 3 ≤ (N : ℕ) := N.2.1
  obtain ⟨σ, hσmon, hσ⟩ := GlobalTheory.SiegRigid.exists_aut m.cart m'.cart
  have hid : σ.hom = 𝟙 o'.A := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre GlobalTheory.laws_without_cohomology.1 o'.A o'.ab σ.hom
      (IsMonHom.one_hom σ.hom) ?_
    intro t
    let K := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫
      S'.fromSpecResidueField t
    refine ⟨Sp K, pullback o'.A.hom j, j, pullback.fst o'.A.hom j, pullback.snd o'.A.hom j,
      IsLocalRing.closedPoint K, ?_, IsPullback.of_hasPullback _ _, ?_⟩
    · exact Scheme.fromSpecResidueField_apply t _
    · apply m'.cart.1.hom_ext
      · rw [Category.assoc, hσ, eq_at_point hN m m' j]
      · rw [Category.assoc, Over.w]
  rw [← hσ, hid, Over.id_left, Category.id_comp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSigmaFEt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_sigma_point {W : Scheme.{0}} {I : Type} (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ ∐ fun _ : I => W) :
    ∃ (i : I) (y' : Spec (CommRingCat.of K) ⟶ W), y' ≫ Sigma.ι (fun _ : I => W) i = y := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk (fun _ : I => W)).surjective (y pt)
  rw [sigmaMk_mk] at hw
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q pt]
  exact ⟨w, hw⟩

private theorem card_sigma_fibre {Y Z : Scheme.{0}} (s : Y ⟶ Z) (I : Type) (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ Z) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} =
      Nat.card I * Nat.card {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} := by
  let F : I × {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} →
      {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} :=
    fun q => ⟨q.2.1 ≫ Sigma.ι (fun _ : I => Y) q.1, by
      rw [Category.assoc, Sigma.ι_desc]
      exact q.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
      have h' : a ≫ Sigma.ι (fun _ : I => Y) i = b ≫ Sigma.ι (fun _ : I => Y) j :=
        congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hab : a = b := (cancel_mono _).mp h'
        subst hab
        rfl
      · exfalso
        have hE := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) ⟨h'⟩ hij
        obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
        exact hE.false p
    · rintro ⟨y, hy⟩
      obtain ⟨i, y', rfl⟩ := exists_sigma_point K y
      refine ⟨⟨i, y', ?_⟩, rfl⟩
      rw [Category.assoc, Sigma.ι_desc] at hy
      exact hy
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

theorem UpperTheory.Gal.G3.pSigmaFEt :
    SigmaFEt := by
  intro Y Z s d I _ hs
  obtain ⟨hfin, het, hcard⟩ := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hid : IsFinite (Sigma.desc fun _ : I => 𝟙 Y) := by
    have h1 := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y n
    have h2 : IsFinite ((Sigma.reindex e (fun _ : Fin n => Y)).hom ≫
        Sigma.desc fun _ : Fin n => 𝟙 Y) := inferInstance
    have h3 : (Sigma.desc fun _ : I => 𝟙 Y) =
        (Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y := by
      refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [Sigma.ι_reindex_hom (f := fun _ : Fin n => Y) e i]
      rw [Sigma.ι_desc]
    rw [h3]
    exact h2
  have hfac : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 Y) ≫ s := by
    refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
    simp
  have hloc : IsZariskiLocalAtSource @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]
    infer_instance
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{0}) fun _ => het
  · intro K _ _ x
    rw [card_sigma_fibre, hcard]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSumFn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {m j : X.ι} {k h : G}
    (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.admitted m j (k * h) := by
  refine ⟨X.Δ.mul_mem (X.K_le j k hk) hh.1, fun u hu => ?_⟩
  have h3 := (X.K j).mul_mem ((X.K j).mul_mem hk (hh.2 u hu)) ((X.K j).inv_mem hk)
  have e : k * h * u * (k * h)⁻¹ = k * (h * u * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact h3

private theorem pl_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
    {m j : X.ι} {k h : G} (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.pl T m j (k * h) = X.pl T m j h := by
  have a := isAdmissible_flagPair_of_unitriangular_left_automorphism X hk hh
  have e : X.tr m j (k * h) a.1 a.2 = X.tr m j h hh.1 hh.2 := by
    rw [← X.tr_mul m j j h k hh.1 hh.2 (X.K_le j k hk)
      (fun u hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)) a.1 a.2,
      X.tr_self j k _ _ hk, Category.comp_id]
  unfold Tower.pl
  rw [dif_pos a, dif_pos hh]
  simp only [e]

theorem UpperTheory.Gal.G3.pSumFn :
    SumFn.{u} := by
  classical
  intro B G _ X F _ T m j A _ e he f hf
  have hmem : ∀ (a : A) (y : G), e a * y ∈ X.K j ↔ (y : G ⧸ X.K j) = (((e a)⁻¹ : G) : G ⧸ X.K j) := by
    intro a y
    rw [eq_comm, QuotientGroup.eq, inv_inv]
  have hex : ∀ g, f g ≠ 0 → ∃ a, e a * g ∈ X.K j := by
    intro g hg
    by_contra hn
    have : IsEmpty {a : A // e a * g ∈ X.K j} := ⟨fun a => hn ⟨a.1, a.2⟩⟩
    exact hg (by rw [hf, Nat.card_of_isEmpty, Nat.cast_zero])
  have h1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := by
    intro g hg
    obtain ⟨a, ha⟩ := hex g hg
    have hk : g⁻¹ = (e a * g)⁻¹ * e a := by group
    rw [hk]
    exact isAdmissible_flagPair_of_unitriangular_left_automorphism X ((X.K j).inv_mem ha) (he a)
  set Fq : A → G ⧸ X.K j := fun a => (((e a)⁻¹ : G) : G ⧸ X.K j) with hFq
  refine ⟨h1, fun hl => ⟨fun k hk g => ⟨hl k hk g, ?_⟩, fun g hg => (h1 g hg).1, ?_⟩, ?_⟩
  · rw [hf, hf]
    have h2 : ∀ a, e a * (g * k) ∈ X.K j ↔ e a * g ∈ X.K j := fun a => by
      rw [← _root_.mul_assoc]
      exact Subgroup.mul_mem_cancel_right _ hk
    simp only [h2]
  · refine (Set.finite_range Fq).subset fun y hy => ?_
    obtain ⟨a, ha⟩ := hex _ hy
    refine ⟨a, ?_⟩
    have := (hmem a y.out).1 ha
    rw [QuotientGroup.out_eq'] at this
    exact this.symm
  · intro x
    have hpl : ∀ a, X.pl T m j (e a) x = X.pl T m j (Fq a).out⁻¹ x := by
      intro a
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (X.K j) (e a)⁻¹
      have h2 : (Fq a).out⁻¹ = (k : G)⁻¹ * e a := by
        simp only [hFq, hk, mul_inv_rev, inv_inv]
      rw [h2, pl_left X T ((X.K j).inv_mem k.2) (he a)]
    have hfy : ∀ y : G ⧸ X.K j, f y.out = ((Finset.univ.filter (fun a => Fq a = y)).card : F) := by
      intro y
      have h2 : Nat.card {a : A // e a * y.out ∈ X.K j} = (Finset.univ.filter (fun a => Fq a = y)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hmem, QuotientGroup.out_eq', eq_comm]
      rw [hf, h2]
    have hsupp : Function.support (fun y : G ⧸ X.K j => f y.out • X.pl T m j y.out⁻¹ x) ⊆
        ↑(Finset.univ.image Fq) := by
      intro y hy
      by_contra hn
      apply hy
      have h0 : Finset.univ.filter (fun a => Fq a = y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro a _ ha
        exact hn (by simpa using ⟨a, ha⟩)
      simp only [hfy, h0, Finset.card_empty, Nat.cast_zero, zero_smul]
    rw [finsum_eq_sum_of_support_subset _ hsupp,
      ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Fq) (g := Fq)
        (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hfy, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hpl a, (Finset.mem_filter.1 ha).2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTatePull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTatePull :
    TatePull := by
  intro p _ D R _ _ gb S S' s s' f N o o' m k _ t
  have hT := HeckeRestrict.tate_pullback D.toG o.A o'.A o.act o'.act o.P o'.P o.isLB o'.isLB f m.φ m.φ₂
    m.cart m.sq m.act m.pol k t
  have hpt : ∀ y, (toUnit (Over.mk (t ≫ f)) ≫ o.eta y).left = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left, m.eta y]
    exact Category.assoc _ _ _
  have hpt' : ∀ y, (toUnit (Over.mk t) ≫ o'.eta y).left ≫ m.φ = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left]
    exact Category.assoc _ _ _
  refine ⟨fun I => ?_, fun I' => ?_⟩
  · obtain ⟨I', hI'⟩ := hT.2 I
    refine ⟨I', fun hI y => ?_, fun n x => (hI' n x).symm⟩
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hpt', ← hpt, hI y, hI' N y]
    · rw [Over.w, Over.w]
  · obtain ⟨I, hI⟩ := hT.1 I'
    refine ⟨I, fun hI' y => ?_, fun n x => (hI n x).symm⟩
    apply Over.OverMorphism.ext
    rw [hpt, hI N y, ← hI' y, hpt']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransFree :
    KNCong → TransFree := by
  intro hK p _ D G L R _ _ gb k _ _ s N o u hu hT
  obtain ⟨-, -, -, -, hp⟩ := hT
  obtain ⟨I', I'', h', h'', hr⟩ := hp k (𝟙 _) (Spec.preimage (𝟙 _ ≫ s)).hom (by
    simp [spMap])
  refine hK p D G L N.1 (by have := N.2.1; omega) N.2.2 u hu fun x => ?_
  exact (hr N.1 (by have := N.2.1; omega) N.2.2 x x).1 (by
    rw [← h' x, ← h'' x]; simp)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitCart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitCart :
    TransIso → WitCart := by
  intro hI p _ D G L R _ _ gb N' N X' X u hu π Φ hW
  obtain ⟨-, o, ψ, φ, hT, rfl⟩ := hW
  have hψ : IsIso ψ := hI p D G L R gb X'.X X'.s N' N X'.univ o ψ u hu hT
  have hl : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget _).map ψ))
  have h₁ : IsPullback ψ.left X'.univ.A.hom o.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz φ.cart.1
  rwa [Category.id_comp] at h₂
end

