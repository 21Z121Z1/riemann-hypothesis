import Development.EtaleCohomology.TateTwists.Bundle0019
import Development.EtaleCohomology.TateTwists.Bundle0020
import Development.EtaleCohomology.TateTwists.Bundle0021

-- bundled from Development.EtaleCohomology.TateTwists.TPaTensUnivPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

abbrev tl {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)

theorem tu_ext {I J : Cx R} {U : Scheme.{0}} {w : ℤ} {M : Type 1} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f g : Tens I J U w →ₗ[ULift.{1} R] M}
    (h : ∀ p a b, f (tl p a b) = g (tl p a b)) : f = g :=
  DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => h p a b

theorem tu_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (tl p a b) = tl p (Sec.res g a) (Sec.res g b) := by
  simp [tl, Tens.res, DirectSum.lmap_lof]

theorem tu_lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (tl p a b) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [tl, Pair.lift, DirectSum.toModule_lof]

theorem tu_sec_res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem tu_sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  simp [Sec.res]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_id, ModuleCat.hom_id, LinearMap.id_apply]
    rw [tu_res_lof, tu_sec_res_id, tu_sec_res_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tu_res_lof, tu_res_lof, tu_res_lof, tu_sec_res_comp, tu_sec_res_comp]

theorem tu_lift_nat {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    refine tu_ext fun p a b => ?_
    simp only [LinearMap.comp_apply]
    rw [tu_res_lof, tu_lift_lof, tu_lift_lof, ← μ.nat]
  exact LinearMap.congr_fun this x

def Lf {I J K : Cx R} (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality V U g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact tu_lift_nat μ g.unop w x

theorem tu_locInj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U x' y' hxy
  let x : Tens I J U.unop w := x'
  let y : Tens I J U.unop w := y'
  have hxy' : τ.lift U.unop w x = τ.lift U.unop w y := hxy
  have h0 : τ.lift U.unop w (x - y) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr hxy'
  obtain ⟨S, hS, hP⟩ := hτ.2 U.unop w (x - y) h0
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  have h1 : Tens.res g w (x - y) = 0 := hP V g hg
  rw [map_sub, sub_eq_zero] at h1
  exact h1

theorem tu_locSurj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U y
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  obtain ⟨x, hx⟩ := hP V g hg
  exact ⟨x, hx⟩

theorem etaleTensorPairingLift_isSheafifyLocalIso {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (Lf τ w) := by
  have := tu_locInj τ hτ w
  have := tu_locSurj τ hτ w
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

def uf {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) : (T.X w).obj ⟶ (K.X w).obj :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose

theorem uf_spec {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) :
    Lf τ w ≫ uf τ hτ μ w = Lf μ w :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose_spec

theorem uf_lift {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) (U : Scheme.{0})
    (x : Tens I J U w) : ((uf τ hτ μ w).app (op U)).hom (τ.lift U w x) = μ.lift U w x := by
  have := congrArg (fun φ => (φ.app (op U)).hom x) (uf_spec τ hτ μ w)
  exact this

theorem uf_mul {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    ((uf τ hτ μ w).app (op U)).hom (τ.mul U s t w h a b) = μ.mul U s t w h a b := by
  have := uf_lift τ hτ μ w U (tl (w := w) ⟨(s, t), h⟩ a b)
  rwa [tu_lift_lof, tu_lift_lof] at this

theorem uf_comm {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (i : ℤ) :
    uf τ hτ μ i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ uf τ hτ μ (i + 1) := by
  apply ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ i) _ (K.X (i + 1)).property).1
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (tu_ext fun p a b => ?_))
  obtain ⟨⟨s, t⟩, h⟩ := p
  simp only [NatTrans.comp_app, ModuleCat.hom_comp]
  change ((K.d i (i + 1)).hom.app U).hom (((uf τ hτ μ i).app (op U.unop)).hom (τ.lift U.unop i (tl _ a b))) =
    ((uf τ hτ μ (i + 1)).app (op U.unop)).hom (((T.d i (i + 1)).hom.app U).hom (τ.lift U.unop i (tl _ a b)))
  rw [tu_lift_lof, uf_mul]
  have l1 := μ.leibniz U.unop s t i h a b
  have l2 := τ.leibniz U.unop s t i h a b
  simp only [Sec.map] at l1 l2
  rw [l1, l2, map_add, Units.smul_def, Units.smul_def, map_zsmul, uf_mul, uf_mul]

def uc {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) : T ⟶ K where
  f w := ⟨uf τ hτ μ w⟩
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    ext1
    exact uf_comm τ hτ μ i

theorem t_pa_tens_univ_of : t_pa_tens_univ := by
  intro R _ I J T K τ hτ μ
  refine ⟨uc τ hτ μ, fun U s t w h a b => ?_⟩
  simp only [HomologicalComplex.id_f, pa_sec_map_id]
  exact uf_mul τ hτ μ U s t w h a b

end LateralTheory.EtaleFoundations
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensPrePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations
namespace TTP

variable {R : Type} [CommRing R]

noncomputable section

abbrev dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) : Sec (I.X s) U →ₗ[ULift.{1} R] Sec (I.X (s + 1)) U :=
  ((I.d s (s + 1)).hom.app (op U)).hom

theorem dI_dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) : dI I U (s + 1) (dI I U s a) = 0 := by
  have h := congrArg (fun f => ((f.hom.app (op U)).hom a)) (I.d_comp_d s (s + 1) (s + 1 + 1))
  exact h.trans (by simp)

theorem dI_res (I : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec (I.X s) U) :
    dI I V s (((I.X s).obj.map g.op).hom a) = ((I.X (s + 1)).obj.map g.op).hom (dI I U s a) := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f a) ((I.d s (s + 1)).hom.naturality g.op)
  exact h

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map (dI I U p.1.1) LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id (dI J U p.1.2)))

theorem dT_of (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s + 1, t), by omega⟩ (dI I U s a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t + 1), by omega⟩ (a ⊗ₜ dI J U t b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), dT, DirectSum.toModule_lof]
  simp [DirectSum.lof_eq_of]

theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : (dT I J U (w + 1)).comp (dT I J U w) = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.zero_apply]
  rw [dT_of, map_add, map_zsmul, dT_of, dT_of]
  simp [dI_dI, Int.negOnePow_succ]

theorem res_of (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) V ⊗[ULift.{1} R] Sec (J.X q.1.2) V)
      ⟨(s, t), h⟩ (((I.X s).obj.map g.op).hom a ⊗ₜ ((J.X t).obj.map g.op).hom b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, DirectSum.lof_eq_of]

theorem res_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.id_apply]
  rw [res_of]
  simp

theorem res_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = Tens.res f w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, res_of, res_of]
  simp

theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, dT_of, dT_of, map_add, map_zsmul, res_of, res_of, dI_res, dI_res]

def PF (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext
    simp only [unop_id, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact res_id I J U.unop w
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [unop_comp, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact res_comp I J g.unop f.unop w

def dN (I J : Cx R) (w : ℤ) : PF I J w ⟶ PF I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    apply ModuleCat.hom_ext
    simp only [PF, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact dT_res I J g.unop w

theorem dN_dN (I J : Cx R) (w : ℤ) : dN I J w ≫ dN I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  simp only [NatTrans.comp_app, dN, NatTrans.app_zero, ModuleCat.hom_zero]
  exact dT_dT I J U.unop w

def PC (I J : Cx R) : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (fun w => PF I J w) (fun w => dN I J w) (fun w => dN_dN I J w)

def tensPre (I J : Cx R) : TensPre I J where
  P := PC I J
  e U w := LinearEquiv.refl (ULift.{1} R) (Tens I J U w)
  nat g w x := rfl
  leibniz U s t w h a b := by
    simp only [PC]
    rw [CochainComplex.of_d]
    exact (dT_of I J U s t w h a b).trans (congrArg (HAdd.hAdd _) (Units.smul_def _ _).symm)

end

end TTP

theorem tt_tens_pre_of : tt_tens_pre := fun _ _ I J => ⟨TTP.tensPre I J⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TwSecLocPfR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.EtaleFoundations.TwSecLocPf

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction f using Finsupp.induction with
  | zero =>
    refine loc_mono (loc_true V) fun W h _ => ⟨0, ?_⟩
    rw [zero_smul, Submodule.Quotient.mk_zero]
    exact map_zero ((twF q i).map h.appTop).hom
  | single_add ξ b g _ _ ih =>
    refine loc_mono (loc_and (hZ q V ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
      ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
    rw [Submodule.Quotient.mk_add]
    refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
    rw [hc, twF_map_mk, Finsupp.mapDomain_single,
      twF_single_pow q i _ _ _ a ha b, add_smul]
    rfl

theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  refine (LateralTheory.EtaleFoundations.TwLocPf.ofRings_sec_res (twF q i) h x).trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

-- bundled from Development.EtaleCohomology.TateTwists.acycIffPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.acycIffPf

variable {R : Type} [CommRing R]

abbrev ev (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem app_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem iCycles_inj (S : ShortComplex (Shv R)) (U : Scheme.{0}) :
    Function.Injective (Sec.map S.iCycles (U := U)) := by
  have : Mono ((ev U).map S.iCycles) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem iCycles_surj (S : ShortComplex (Shv R)) (U : Scheme.{0}) (z : Sec S.X₂ U) (hz : Sec.map S.g z = 0) :
    ∃ c : Sec S.cycles U, Sec.map S.iCycles c = z := by
  let S' : ShortComplex (Shv R) := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hS' : S'.Exact := S'.exact_of_f_is_kernel S.cyclesIsKernel
  have hE : (S'.map (ev U)).Exact := hS'.map_of_mono_of_preservesKernel (ev U) (inferInstanceAs (Mono S.iCycles)) inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hE z hz

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔
    ∀ (U : Scheme.{0}) (z : Sec S.X₂ U), Sec.map S.g z = 0 →
      Loc U fun V g => ∃ y : Sec S.X₁ V, Sec.map S.f y = Sec.res g z := by
  rw [S.exact_iff_epi_toCycles, ← Sheaf.isLocallySurjective_iff_epi' _ S.toCycles]
  constructor
  · intro h U z hz
    obtain ⟨c, rfl⟩ := iCycles_surj S U z hz
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} S.toCycles.hom (U := op U) c, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h1 : Sec.map S.f t = Sec.map S.iCycles (Sec.map S.toCycles t) := by
      rw [← app_comp, S.toCycles_i]
    rw [h1, ← map_res]
    exact congrArg _ ht
  · intro h
    constructor
    intro U c
    obtain ⟨Sv, hSv, hP⟩ := h U (Sec.map S.iCycles c) (by rw [← app_comp, S.iCycles_g]; rfl)
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hSv
    intro V g hg
    obtain ⟨y, hy⟩ := hP V g hg
    refine ⟨y, iCycles_inj S V ?_⟩
    change Sec.map S.iCycles (Sec.map S.toCycles y) = Sec.map S.iCycles (Sec.res g c)
    rw [← app_comp, S.toCycles_i, hy, map_res]

end LateralTheory.EtaleFoundations.acycIffPf

open LateralTheory.EtaleFoundations.acycIffPf in
theorem LateralTheory.EtaleFoundations.acyc.acycIff_of : LateralTheory.EtaleFoundations.acyc.acycIff := by
  intro R _ C
  unfold LateralTheory.EtaleFoundations.acyc.LocAcyc
  constructor
  · intro h U n z hz
    have := (HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)).1 (h n)
    exact (exact_iff _).1 this U z hz
  · intro h n
    rw [HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)]
    exact (exact_iff _).2 fun U z hz => h U n z hz
end

