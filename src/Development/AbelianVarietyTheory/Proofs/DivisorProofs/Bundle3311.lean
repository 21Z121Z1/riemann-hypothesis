import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinates
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.LawCoord

theorem evA_X {k : Type} [CommRing k] {σ : Type} [Finite σ] {A : Type} [CommRing A] [Algebra k A]
    (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ) : evA k x hx (X i) = x i := by
  have ha : HasSubst (fun i => (C (x i) : MvPowerSeries Empty A)) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  change constantCoeff (substAlgHom (R := k) ha (X i : MvPowerSeries σ k)) = x i
  rw [substAlgHom_apply, subst_X ha]
  simp

theorem main : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d),
    (∃ μ, c.IsLawOf μ) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
      (∀ i, constantCoeff (μ i) = 0) ∧ ∀ n f, c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) ∧
        c.ev₂ n (cob1 μ f) = cobOne k (G.A n) (c.ev n f) := by
  intro p k _ d G c
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h := fun i => ((GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => Coalgebra.comul (R := k) (c.x n i))
      (fun n => by rw [pullTwo_comul]; exact congrArg _ (c.res n i))).exists
    choose μ hμ using h
    exact ⟨μ, fun n i => hμ i n⟩
  have hconst : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    have h := (GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c 0).2.2.2 (μ i)
    rw [← h, hμ 0 i]
    have key : ∀ t : G.A 0 ⊗[k] G.A 0, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A 0))
        (Bialgebra.counitAlgHom k (G.A 0)) (fun _ _ => Commute.all _ _) t =
        Coalgebra.counit (R := k) (TensorProduct.lid k (G.A 0)
          (LinearMap.rTensor (G.A 0) (Coalgebra.counit (R := k) (A := G.A 0)) t)) := by
      intro t
      induction t with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [key, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
    exact c.aug 0 i
  refine ⟨hconst, fun n f => ?_⟩
  have hs : c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) := by
    have hy : ∀ i, IsNilpotent (Coalgebra.comul (R := k) (c.x n i)) := fun i =>
      (c.nil n i).map (Bialgebra.comulAlgHom k (G.A n))
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by rw [Chart.ev₂, evA_X]; exact c.nil₂ n t) μ hconst _ hy (fun i => hμ n i) f
    have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      (Bialgebra.comulAlgHom k (G.A n)) (c.x n) (c.nil n) _ hy (fun i => rfl) f
    rw [h1, ← h2]
    rfl
  refine ⟨hs, ?_⟩
  have he := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n
  rw [cob1, map_sub, map_sub, hs, he.1, he.2.1, cobOne_apply]

end GlobalTheory.LawCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUnique
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isMapOf_existsUnique_and : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ f : G ⟶ H, (∃! φ, c.IsMapOf c' f φ) ∧ ∀ (φ : Fin e → MvPowerSeries (Fin d) k), c.IsMapOf c' f φ → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n, (∀ g, c.ev n (subst φ g) = f.app n (c'.ev n g)) ∧ ∀ s, c.ev₂ n (pull2 φ s) = pullbackTwo (f.app n) (c'.ev₂ n s) := by
  intro p k _ d e G H c c' f
  have hone := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2
  have hcomp : ∀ j n, G.res n (f.app (n + 1) (c'.x (n + 1) j)) = f.app n (c'.x n j) := fun j n => by
    rw [res_app, c'.res]
  refine ⟨?_, ?_⟩
  · choose φ hφ _ using fun j => hone (fun n => f.app n (c'.x n j)) (hcomp j)
    refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => ?_⟩
    obtain ⟨g, -, hg⟩ := hone (fun n => f.app n (c'.x n j)) (hcomp j)
    exact (hg (ψ j) fun n => hψ n j).trans (hg (φ j) fun n => hφ j n).symm
  intro φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d (G.A 0) (c.x 0) (c.nil 0) (c.aug 0) (φ j)).1
    change Coalgebra.counit (R := k) (c.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, CoalgHomClass.counit_comp_apply, c'.aug]
  refine ⟨hconst, fun n => ⟨fun g => ?_, fun s => ?_⟩⟩
  · have hy : ∀ j, IsNilpotent (f.app n (c'.x n j)) := fun j => (c'.nil n j).map (f.app n)
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (G.A n)).1 (Fin d) (c.ev n)
      (fun t => by
        change IsNilpotent (evA k (c.x n) (c.nil n) (X t))
        rw [evA_X]; exact c.nil n t) φ hconst _ hy (fun j => hφ n j) g
    rw [h1]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (H.A n)).2 (G.A n) (f.app n : H.A n →ₐ[k] G.A n) (c'.x n)
      (c'.nil n) _ hy (fun _ => rfl) g).symm
  · let F : H.A n ⊗[k] H.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      Algebra.TensorProduct.map (f.app n : H.A n →ₐ[k] G.A n) (f.app n : H.A n →ₐ[k] G.A n)
    have hy : ∀ i, IsNilpotent (F (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map F
    have hev := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n
    have ha : ∀ i, constantCoeff ((Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) :
        Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k) i) = 0 := by
      intro i
      have hc := hev.2.2.2
      cases i with
      | inl j =>
        rw [Sum.elim_inl, ← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
      | inr j =>
        rw [Sum.elim_inr, ← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by
        change IsNilpotent (evA k (c.x₂ n) (c.nil₂ n) (X t))
        rw [evA_X]; exact c.nil₂ n t) _ ha _ hy
      (fun i => by
        cases i with
        | inl j =>
          simp only [Sum.elim_inl]
          rw [hev.1, hφ n j]
          show _ = F (c'.x n j ⊗ₜ 1)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
        | inr j =>
          simp only [Sum.elim_inr]
          rw [hev.2.1, hφ n j]
          show _ = F (1 ⊗ₜ c'.x n j)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl) s
    have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n ⊗[k] G.A n) F
      (c'.x₂ n) (c'.nil₂ n) _ hy (fun _ => rfl) s
    have h3 : pullbackTwo (f.app n) (c'.ev₂ n s) = F (c'.ev₂ n s) := by
      induction (c'.ev₂ n s) with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b => rfl
    unfold pull2 at2
    rw [h1, h3]
    exact h2.symm

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormsRestrictionAffineLiftBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LevLift

variable (D : Data) (Λ : Lift D) (n : ℕ)

abbrev CC : Type 1 := (LevE D.κ D.t D.i (n + 1)).FullSubcategory

variable {D n}

theorem hom_ext' {T T' : CC D n} {f g : T ⟶ T'} (h : f.hom.hom.1 = g.hom.hom.1) : f = g :=
  ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Subtype.ext h))

def opn (T : CC D n) : AffOp D.X := Opposite.op ⟨T.obj.obj.U, T.obj.property⟩

variable (D n) in

def qq : CC D n ⥤ AffOp D.X where
  obj T := opn T
  map f := (homOfLE (show (⟨_, _⟩ : D.X.affineOpens) ≤ ⟨_, _⟩ from f.hom.hom.2)).op
  map_id _ := rfl
  map_comp _ _ := rfl

theorem mem_of_hom {T T' : Thick D.κ D.t} (f : T ⟶ T') {U : D.X.Opens} (h : ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U) :
    ⊤ ≤ (T'.x ≫ D.i) ⁻¹ᵁ U := by
  rw [← f.pt, Category.assoc, Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]

theorem cop_ex (T : CC D n) : ∃ (G : Thick D.κ D.t) (l : T.obj.obj.T ⟶ G) (r : Λ.L.obj ((qq D n).obj T) ⟶ G),
    IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l :=
  GlobalTheory.T.exists_coproduct_thickening_affine_lift_poincare D Λ n ((qq D n).obj T) T.obj.obj.T T.property T.obj.obj.mem

def GG (T : CC D n) : Thick D.κ D.t := (cop_ex Λ T).choose

def ll (T : CC D n) : T.obj.obj.T ⟶ GG Λ T := (cop_ex Λ T).choose_spec.choose

def rr (T : CC D n) : Λ.L.obj ((qq D n).obj T) ⟶ GG Λ T := (cop_ex Λ T).choose_spec.choose_spec.choose

theorem isCop (T : CC D n) : IsCop (n + 1) (ll Λ T) (rr Λ T) :=
  (cop_ex Λ T).choose_spec.choose_spec.choose_spec.1

theorem qat_ll (T : CC D n) : (KK D.κ D.t).QAt (ll Λ T) :=
  (cop_ex Λ T).choose_spec.choose_spec.choose_spec.2

def SObj (T : CC D n) : CC D n :=
  ⟨⟨⟨GG Λ T, T.obj.obj.U, T.obj.obj.hU, mem_of_hom (ll Λ T) T.obj.obj.mem⟩, T.obj.property⟩, (isCop Λ T).1⟩

theorem smap_ex {T T' : CC D n} (f : T ⟶ T') : ∃! c : GG Λ T ⟶ GG Λ T',
    ll Λ T ≫ c = f.hom.hom.1 ≫ ll Λ T' ∧ rr Λ T ≫ c = Λ.L.map ((qq D n).map f) ≫ rr Λ T' :=
  (isCop Λ T).2 (GG Λ T') (isCop Λ T').1 _ _

def smap {T T' : CC D n} (f : T ⟶ T') : GG Λ T ⟶ GG Λ T' := (smap_ex Λ f).exists.choose

theorem smap_spec {T T' : CC D n} (f : T ⟶ T') :
    ll Λ T ≫ smap Λ f = f.hom.hom.1 ≫ ll Λ T' ∧ rr Λ T ≫ smap Λ f = Λ.L.map ((qq D n).map f) ≫ rr Λ T' :=
  (smap_ex Λ f).exists.choose_spec

theorem smap_uniq {T T' : CC D n} (f : T ⟶ T') (c : GG Λ T ⟶ GG Λ T')
    (h1 : ll Λ T ≫ c = f.hom.hom.1 ≫ ll Λ T') (h2 : rr Λ T ≫ c = Λ.L.map ((qq D n).map f) ≫ rr Λ T') :
    c = smap Λ f :=
  (smap_ex Λ f).unique ⟨h1, h2⟩ (smap_spec Λ f)

def SS : CC D n ⥤ CC D n where
  obj := SObj Λ
  map f := ObjectProperty.homMk (ObjectProperty.homMk ⟨smap Λ f, f.hom.hom.2⟩)
  map_id T := hom_ext' (smap_uniq Λ (𝟙 T) (𝟙 _) (by simp; rfl)
    (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]; simp)).symm
  map_comp {T T' T''} f g := hom_ext' (smap_uniq Λ (f ≫ g) (smap Λ f ≫ smap Λ g)
    (by rw [← Category.assoc, (smap_spec Λ f).1, Category.assoc, (smap_spec Λ g).1, ← Category.assoc]; rfl)
    (by rw [← Category.assoc, (smap_spec Λ f).2, Category.assoc, (smap_spec Λ g).2, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp])).symm

def uu : 𝟭 (CC D n) ⟶ SS Λ where
  app T := ObjectProperty.homMk (ObjectProperty.homMk ⟨ll Λ T, le_rfl⟩)
  naturality {T T'} f := hom_ext' (smap_spec Λ f).1.symm

variable (h : ∀ U, LevE D.κ D.t D.i (n + 1) (Λ.toE.obj U))

abbrev ell : AffOp D.X ⥤ CC D n := (LevE D.κ D.t D.i (n + 1)).lift Λ.toE h

def ww : qq D n ⋙ ell Λ h ⟶ SS Λ where
  app T := ObjectProperty.homMk (ObjectProperty.homMk ⟨rr Λ T, le_rfl⟩)
  naturality {T T'} f := hom_ext' (smap_spec Λ f).2.symm

def eps : 𝟭 (AffOp D.X) ⟶ ell Λ h ⋙ qq D n where
  app U := 𝟙 U
  naturality _ _ _ := rfl

abbrev KL : Cx (CC D n) := (((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i (n + 1)).ι)

theorem qat_iff {T T' : CC D n} (φ : T ⟶ T') : (KL (D := D) (n := n)).QAt φ ↔ (KK D.κ D.t).QAt φ.hom.hom.1 :=
  Iff.rfl

theorem qat_rr (U : AffOp D.X) : (KK D.κ D.t).QAt (rr Λ ((ell Λ h).obj U)) := by
  set T := (ell Λ h).obj U
  have hc := isCop Λ T
  obtain ⟨σ, ⟨h1, h2⟩, -⟩ := hc.2 (GG Λ T) hc.1 (rr Λ T) (ll Λ T)
  have hσ : σ ≫ σ = 𝟙 _ := by
    obtain ⟨c, -, hu⟩ := hc.2 (GG Λ T) hc.1 (ll Λ T) (rr Λ T)
    exact (hu (σ ≫ σ) ⟨(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ σ) h1).trans h2),
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ σ) h2).trans h1)⟩).trans
      (hu (𝟙 _) ⟨Category.comp_id _, Category.comp_id _⟩).symm
  have hi : IsIso σ := ⟨σ, hσ, hσ⟩
  obtain ⟨hiso, hcomp, -⟩ := GlobalTheory.T.fourTermComplex_quasiIsoAt_formal_properties (Thick D.κ D.t) (KK D.κ D.t)
  exact h1 ▸ hcomp _ _ _ _ _ (qat_ll Λ T) (hiso _ _ σ)

theorem qat_map_id (U : AffOp D.X) {B : Thick D.κ D.t} (f : Λ.L.obj U ⟶ B) (hf : (KK D.κ D.t).QAt f) :
    (KK D.κ D.t).QAt (Λ.L.map (𝟙 U) ≫ f) := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact hf

theorem resMap_bij : (KL (D := D) (n := n)).resMap (ell Λ h) |>.Bij := by
  refine GlobalTheory.T.fourTermComplex_restriction_bijective_collapse (CC D n) (AffOp D.X) KL (ell Λ h) (qq D n) (SS Λ) (uu Λ) (ww Λ h) (eps Λ h)
    (fun T ↦ qat_ll Λ T) (fun U ↦ ?_)
  rw [qat_iff]
  exact qat_map_id Λ U _ (qat_rr Λ h U)

end GlobalTheory.PDForm.LevLift

theorem GlobalTheory.PDForm.levLift_resMap_bij : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (h : ∀ U, LevE D.κ D.t D.i (n + 1) (Λ.toE.obj U)),
    ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i (n + 1)).ι).resMap
      ((LevE D.κ D.t D.i (n + 1)).lift Λ.toE h)).Bij :=
  fun _ Λ _ h ↦ GlobalTheory.PDForm.LevLift.resMap_bij Λ h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcIntegrationByParts
section
set_option autoImplicit false

open MeasureTheory Filter
open GlobalTheory GlobalTheory.CxForm GlobalTheory.LineForm
open GlobalTheory.GoodMetric (coordVec)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Topology

namespace GlobalTheory.CxForm.ByParts

section Point

variable {n : ℕ}

theorem delAt_fun (u : V n → ℂ) (x : V n) :
    delAt (fun y => algebraMap ℂ (Alt n) (u y)) x = ∑ a, del u x (coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun (u : V n → ℂ) (x : V n) :
    dbarAt (fun y => algebraMap ℂ (Alt n) (u y)) x = ∑ a, dbar u x (coordVec a) • dzb a := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dzb_mul_dz (a b : Fin n) : dzb b * dz a = -(dz a * dzb b) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem dbarAt_delAt_fun {u : V n → ℂ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    dbarAt (delAt fun y => algebraMap ℂ (Alt n) (u y)) v = -delAt (dbarAt fun y => algebraMap ℂ (Alt n) (u y)) v := by
  have hconst := (delAt_dbarAt_linear_local n v).2.2.2.2
  have e₁ : (delAt fun y => algebraMap ℂ (Alt n) (u y)) = fun x => ∑ a, del u x (coordVec a) • dz a :=
    funext (delAt_fun u)
  have e₂ : (dbarAt fun y => algebraMap ℂ (Alt n) (u y)) = fun x => ∑ a, dbar u x (coordVec a) • dzb a :=
    funext (dbarAt_fun u)
  have hd (a : Fin n) : DifferentiableAt ℝ (fun x => del u x (coordVec a)) v := by
    have h1 : DifferentiableAt ℝ (del u) v :=
      (contDiffAt_del (m := 1) hu (by norm_num)).differentiableAt (by simp)
    exact ((ContinuousLinearMap.apply ℂ ℂ (coordVec a)).restrictScalars ℝ).differentiableAt.comp v h1
  rw [e₁, e₂, dbarAt_sum_smul (c := fun a x => del u x (coordVec a)) (F := fun a _ => dz a) hd
      (fun _ _ => differentiableAt_const _),
    DelForm.delAt_sum_smul (fun a x => dbar u x (coordVec a)) (fun a _ => dzb a)
      (fun a => differentiableAt_dbar_apply hu _) (fun _ _ => differentiableAt_const _)]
  simp only [(hconst _).1, (hconst _).2, smul_zero, add_zero, DelForm.dOne, Finset.sum_mul, smul_mul_assoc,
    ← ddbar_eq_dbar_del hu, ← ddbar_eq_del_dbar hu, dzb_mul_dz, smul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

end Point

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem target_mem (x : A.Pt) : (A.e x.1.1).target ∈ 𝓝 x.crd :=
  (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)

theorem diff_coef {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt (target_mem A x)).differentiableAt (by simp)

theorem loc_mul (α β : A.Fld) (i : A.ι) : A.loc (α * β) i = fun v => A.loc α i v * A.loc β i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (mul_zero _).symm]

theorem loc_del_dbar (α : A.Fld) (i : A.ι) {v : V n} (hv : v ∈ (A.e i).target) :
    A.loc (A.del α) i v = delAt (A.loc α i) v ∧ A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
  constructor <;> rw [HolAtlas.loc, dif_pos hv]
  · exact congrArg (delAt (A.loc α i)) ((A.e i).right_inv hv)
  · exact congrArg (dbarAt (A.loc α i)) ((A.e i).right_inv hv)

theorem loc_fn (g : M → ℝ) (i : A.ι) {v : V n} (hv : v ∈ (A.e i).target) :
    A.loc (A.fn g) i =ᶠ[𝓝 v] fun w => algebraMap ℂ (Alt n) (g ((A.e i).symm w) : ℂ) :=
  eventually_of_mem ((A.e i).open_target.mem_nhds hv) fun w hw => by
    rw [HolAtlas.loc, dif_pos hw]
    rfl

theorem dbar_del_fn {g : M → ℝ} (hg : A.SmoothOn Set.univ fun y => (g y : ℂ)) :
    A.dbar (A.del (A.fn g)) = -A.del (A.dbar (A.fn g)) := by
  funext x
  have hgerm := fun v => (delAt_dbarAt_linear_local n v).2.2.2.1
  have h₁ : A.loc (A.del (A.fn g)) x.1.1 =ᶠ[𝓝 x.crd]
      delAt fun w => algebraMap ℂ (Alt n) (g ((A.e x.1.1).symm w) : ℂ) :=
    eventually_of_mem (target_mem A x) fun v hv =>
      (loc_del_dbar A _ _ hv).1.trans (hgerm v _ _ (loc_fn A g _ hv)).1
  have h₂ : A.loc (A.dbar (A.fn g)) x.1.1 =ᶠ[𝓝 x.crd]
      dbarAt fun w => algebraMap ℂ (Alt n) (g ((A.e x.1.1).symm w) : ℂ) :=
    eventually_of_mem (target_mem A x) fun v hv =>
      (loc_del_dbar A _ _ hv).2.trans (hgerm v _ _ (loc_fn A g _ hv)).2
  have hu : ContDiffAt ℝ 2 (fun w => (g ((A.e x.1.1).symm w) : ℂ)) x.crd :=
    (((hg x.1.1).mono fun v hv => ⟨hv, trivial⟩).contDiffAt (target_mem A x)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [Pi.neg_apply, HolAtlas.dbar, HolAtlas.del, (hgerm _ _ _ h₁).2, (hgerm _ _ _ h₂).1]
  exact dbarAt_delAt_fun hu

theorem dbar_del_fn_mul {g : M → ℝ} {ψ : A.Fld} (hd : A.IsForm (A.del (A.fn g))) (hψ : A.IsForm ψ) :
    A.dbar (A.del (A.fn g) * ψ) = A.dbar (A.del (A.fn g)) * ψ - A.del (A.fn g) * A.dbar ψ := by
  funext x
  have key := (FormMul.leibniz_of_comm n (A.loc (A.del (A.fn g)) x.1.1) (A.loc ψ x.1.1) x.crd
    (-A.del (A.fn g) x) (diff_coef A hd x) (diff_coef A hψ x)).2 fun a => by
      rw [A.loc_crd, HolAtlas.del,
        ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (loc_fn A g _ (x.ch.map_source x.2))).1, delAt_fun]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, dzb_mul_dz, neg_mul, smul_neg,
        Finset.sum_neg_distrib]
  rw [A.loc_crd ψ x, neg_mul, ← sub_eq_add_neg] at key
  rw [HolAtlas.dbar, loc_mul]
  exact key

end Manifold

theorem integral_fn_mul_ddc : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    A.SmoothOn Set.univ (fun y => (g y : ℂ)) → ∀ ψ : A.Fld, A.IsForm ψ →
      A.integral (A.fn g * A.ddc ψ) = A.integral (A.ddc (A.fn g) * ψ) := by
  intro M _ _ _ _ _ _ n A g hg ψ hψ
  obtain ⟨-, C, L, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  obtain ⟨hfin, hadd, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have S := GlobalTheory.T.integral_del_dbar_zero M n A
  have add : ∀ α β : A.Fld, A.IsForm α → A.IsForm β → A.integral (α + β) = A.integral α + A.integral β := by
    intro α β hα hβ
    simp only [← wInt_one]
    exact (hadd _ α β hα hβ (fun ε => have := hfin α hα ε; integrable_const _)
      (fun ε => have := hfin β hβ ε; integrable_const _)).2
  have fmul : ∀ {α β : A.Fld}, A.IsForm α → A.IsForm β → A.IsForm (α * β) := fun h h' => (C 0 _ _ h h').2.1
  have fsm : ∀ (c : ℂ) {α : A.Fld}, A.IsForm α → A.IsForm (c • α) := fun c _ h => (C c _ _ h h).2.2.1
  have fdel : ∀ {α : A.Fld}, A.IsForm α → A.IsForm (A.del α) := fun h => (C 0 _ _ h h).2.2.2.1
  have fdbar : ∀ {α : A.Fld}, A.IsForm α → A.IsForm (A.dbar α) := fun h => (C 0 _ _ h h).2.2.2.2.1
  have ha : A.IsForm (A.fn g) := A.isForm_fn hg
  have h₁ := fmul ha (fdbar hψ)
  have h₂ := fmul (fdel ha) hψ
  have e₁ : A.del (A.fn g * A.dbar ψ) = A.del (A.fn g) * A.dbar ψ + A.fn g * A.del (A.dbar ψ) :=
    (L (fun x => algebraMap ℂ (Ev n) (g x.pt)) (A.dbar ψ) ha (fdbar hψ)).1
  have e₂ := dbar_del_fn_mul A (fdel ha) hψ
  rw [dbar_del_fn A hg] at e₂
  have e : A.fn g * A.ddc ψ = A.ddc (A.fn g) * ψ + (A.del (HermFrame.kappa • (A.fn g * A.dbar ψ)) +
      A.dbar (HermFrame.kappa • (A.del (A.fn g) * ψ))) := by
    rw [(C _ _ _ h₁ h₁).2.2.2.2.2.2.2.1, (C _ _ _ h₂ h₂).2.2.2.2.2.2.2.2, e₁, e₂, HolAtlas.ddc, HolAtlas.ddc,
      mul_smul_comm, smul_mul_assoc, ← smul_add, ← smul_add, neg_mul]
    congr 1
    abel
  have k₁ := fsm HermFrame.kappa h₁
  have k₂ := fsm HermFrame.kappa h₂
  have k₀ : A.IsForm (A.ddc (A.fn g) * ψ) := fmul (fsm HermFrame.kappa (fdel (fdbar ha))) hψ
  rw [e, add _ _ k₀ (C 0 _ _ (fdel k₁) (fdbar k₂)).1, add _ _ (fdel k₁) (fdbar k₂),
    (S _ k₁).1, (S _ k₂).2, add_zero, add_zero]

end GlobalTheory.CxForm.ByParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSectionFlat
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem unit_at_eqChar_points : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ)) → ∃ s₀ : ArchSec U x Z (flatWt Dw τ), ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s₀.sig) = 0 := by
  intro hP hQ2 hQ3 E _ _ _ H Dw l Xo c r U x hL Z τ _
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := GlobalTheory.T.exists_model_rule_section hP hQ2 hQ3 E H Dw l Xo c r U x hL Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.T.exists_flatWeight_rule_reads_nonvanishing_detSection E H Dw l Xo c Y Z V τ sig hV hs hnv
  have hnorm := GlobalTheory.T.constant_length_of_reading_horizontal_section E H Dw l Xo c r U x hL Z τ Y V sig f hV hs hnv hh hf hR
  choose b hb hb' using fun σ => hnorm _ (goodEmb_goodOf c σ)
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, fun T io y₀ h0 hZ =>
    GlobalTheory.T.rule_section_nowhere_vanishing_real hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩

end GlobalTheory.BdryUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_siegelLevelCover_sharpTheta : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ η ∈ genericPoints F.X, ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ∀ j : ℕ, 1 ≤ j → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (κ : cycAway n →+* o) (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2)) (t : TObj (8 * g) ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J) (x : Sp R ⟶ F.X), R.FG ∧ (∀ y : Ω, ∃ a ∈ R, ∃ c ∈ R, y = a / c) ∧ t.Prim w w' ∧ (∀ (T : Scheme.{0}) (f : T ⟶ Sp R) (P : PolAV T) (φ : P.A.left ⟶ t.A.left), IsGrpPullback P.A t.A f φ → LBIso P.L (t.L.pull φ) → SharpOver F W P (f ≫ x)) ∧ (∀ w, (spMap R.val.toRingHom ≫ x) w = η) ∧ spMap R.val.toRingHom ≫ x ≫ F.s = spMap ((algebraMap o Ω).comp κ) ∧ κ.Finite ∧ ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  first | exact @GlobalTheory.PoincChart.exists_chart | exact GlobalTheory.PoincChart.exists_chart | (intros; apply GlobalTheory.PoincChart.exists_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToPStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelPart_order_prime_to_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B) (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | exact GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_not_dvd <;> assumption)
end

