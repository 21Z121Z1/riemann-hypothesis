import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv.Transport

section Helpers

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_fn_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ a : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = gs r z ⊤ a := by
  obtain ⟨t, hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) s
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, sval_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gs_res r z le trivial _).symm

theorem mem_pow_of_gs {W : Type} [CommRing W] (J : Ideal W) (n : ℕ) (a : W)
    (h : ∀ z, gs (adicLevelι J n) z ⊤ (toΓ W a) = 0) : a ∈ J ^ n := by
  have h1 : (adicLevelι J n).appTop.hom (toΓ W a) = 0 := fn_ext (V := ⊤) fun z _ =>
    (gs_pull (𝟙 _) (adicLevelι J n) z ⊤ trivial _).trans (by
      rw [Category.id_comp, h z]; exact (DVR.gs_zero (𝟙 _) z ⊤ trivial).symm)
  have h2 := congrArg (fun q => q.hom (toΓ W a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [h1, map_zero] at h2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (toΓ W a) = a := by
    simp only [toΓ]; exact Iso.inv_hom_id_apply _ _
  rw [h3] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2.symm

theorem toΓ_hom {W : Type} [CommRing W] (a : Γ(Sp W, ⊤)) :
    toΓ W ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a) = a := by
  simp only [toΓ]; exact Iso.hom_inv_id_apply _ _

end Helpers

theorem exists_adic_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] (φ : R →+* W) (ξ : GtPt D.toPre (Over.mk (spMap φ))) (x' : Over.mk (spMap φ) ⟶ G), IsPointOf U ξ x' → ∀ (b : Sp W ⟶ D.toPre.P.A.left), ξ.b.left = b → ∀ (g' : Frame U.LG.L (Y := Sp W) x'.left) (g : Frame D.toPre.P.L b), g'.IsGen → g.IsGen → FrRel U (T := Sp W) x'.left b g' g → ∀ (k : ℕ) (σ : H0 U.LG.L k) (F : ∀ α, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ F) → ∃ (s : W) (t : D.toPre.X → W), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ (toΓ W s) * (val g' r z JL ^ k).val) ∧ (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ b) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ (toΓ W (t α)) * (val g r z JM ^ k).val) ∧ ∀ e : ℕ, ∃ S : Finset D.toPre.X, (∀ α ∉ S, t α ∈ I.map φ ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map φ ^ (e + 1) := by
  intro R _ _ I D A G _ _ U W _ φ ξ x' hx b hb g' g hg' hg hfr k σ F hexp
  subst hb
  have hL := U.LG.isLB
  have hM := D.toPre.P.isLB

  obtain ⟨a, ha⟩ := exists_fn_of_formal hL
    (φ := Sum.elim (fun _ : Fin 1 => x'.left ≫ 𝟙 G.left) (fun _ : PUnit.{1} => x'.left))
    (ε := Sum.elim (fun _ => (k : ℤ)) (fun _ => -((k : ℤ) * 1)))
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec σ x'.left (LB.invGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ g' k))
      (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg' k)))
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL →
      sval σ (r ≫ x'.left) z JL = gs r z ⊤ a * (val g' r z JL ^ k).val := by
    intro Z r z JL hJL
    have e₁ := (ha Z r z JL hJL).symm.trans (sval_pullMulSec σ x'.left _ _ r z hJL)
    rw [val_inv, show val (GeneratorPullback.powGen U.LG.L _ _ g' k) r z JL = val g' r z JL ^ k from map_pow _ _ _] at e₁
    rw [e₁, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

  have ht : ∀ α, ∃ c : Γ(Sp W, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM →
      sval (F α) (r ≫ ξ.b.left) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ c * (val g r z JM ^ k).val := by
    intro α
    obtain ⟨c, hc⟩ := exists_fn_of_formal hM
      (φ := Sum.elim (fun i => ξ.b.left ≫ D.toPre.famφB α i)
        (Sum.elim (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α) (fun _ : PUnit.{1} => ξ.b.left)))
      (ε := Sum.elim (DegPre.famε k) (Sum.elim DegPre.gtε (fun _ => -((k : ℤ) * 1))))
      (fun U _ h => by
        have e := GlobalTheory.ConstTerm.prod_factors (fun i => h (ξ.b.left ≫ D.toPre.famφB α i)) k
        have e₀ : ∀ i, h (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α i) =
            ![h (ξ.b.left ≫ D.toPre.famφB α 1), h (ξ.b.left ≫ D.toPre.famφB α 2),
              h (ξ.b.left ≫ D.toPre.famφB α 0), h (ξ.b.left ≫ D.toPre.famφB α 3)] i := by
          intro i
          fin_cases i <;> simp [GlobalTheory.ConstTerm.comp_famφB]
        simp only [← e₀] at e
        have e₁ : ξ.b.left ≫ D.toPre.famφB α 0 = ξ.b.left := Category.comp_id _
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← _root_.mul_assoc, e, e₁]
        simp)
      (pullMulSec (F α) ξ.b.left
        (LB.mulGen D.toPre.P.L _ _ _ _ (ξ.s α) (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ g k)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (ξ.isGen α)
          (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg k))))
    refine ⟨c, fun Z r z JM hJM => ?_⟩
    have e₁ := (hc Z r z JM hJM).symm.trans (sval_pullMulSec (F α) ξ.b.left _ _ r z hJM)
    rw [val_mul hJM, val_inv,
      show val (GeneratorPullback.powGen D.toPre.P.L _ _ g k) r z JM = val g r z JM ^ k from map_pow _ _ _] at e₁
    rw [e₁, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  choose c hc using ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a,
    fun α => (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (c α), fun Z r z JL hJL => ?_,
    fun α Z r z JM hJM => ?_, fun e => ?_⟩
  · rw [toΓ_hom]; exact h1 Z r z JL hJL
  · rw [toΓ_hom]; exact hc α Z r z JM hJM
  · set J := I.map φ
    obtain ⟨S, hS⟩ := DVR.expandsAt_val U e k σ F (hexp e)
    have hy₁ : reduction I x' e ≫ fGl I G e = adicLevelι J (e + 1) ≫ x'.left := reduction_fstG I x' e
    obtain ⟨hy₂, hy₃⟩ := (hasCoords_iff U e ξ _ _).1 (hx e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁)
    have gM : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JM, Good D.toPre.P.L z JM := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart hM (ψ z)
      exact ⟨C, hC⟩
    have gL : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JL, Good U.LG.L z JL := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ G.left => exists_chart hL (ψ z)
      exact ⟨C, hC⟩
    refine ⟨S, fun α hα => mem_pow_of_gs J (e + 1) _ fun z => ?_, mem_pow_of_gs J (e + 1) _ fun z => ?_⟩
    · obtain ⟨JM, hJM⟩ := gM z
      have h0 := (hS _ (reduction I x' e) z JM hJM).1 α hα
      rw [hy₂] at h0
      have h2 := hc α _ (adicLevelι J (e + 1)) z JM hJM
      rw [h0, zero_mul] at h2
      rw [toΓ_hom]
      exact (Units.mul_left_eq_zero _).1 h2.symm
    · obtain ⟨JM, hJM⟩ := gM z
      obtain ⟨JL, hJL⟩ := gL z
      have hE := (hS _ (reduction I x' e) z JM hJM).2 (JL (reduction I x' e ≫ fGl I G e)) (hJL _)
      have hw := hfr e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁ z JM JL hJM hJL
      have hsv : DVR.sv U k σ (reduction I x' e ≫ fGl I G e) z (JL (reduction I x' e ≫ fGl I G e)) =
          sval σ (adicLevelι J (e + 1) ≫ x'.left) z JL := by
        rw [← hy₁]; exact (sval_of σ _ z JL _ fun _ => by rw [Category.comp_id]).symm
      have hwv : DVR.wv U e (reduction I x' e) z (JM (reduction I x' e ≫ pGl U e))
          (JL (reduction I x' e ≫ fGl I G e)) = wVal U e z JM JL (reduction I x' e) := rfl
      have hterm : ∀ α ∈ S, sval (F α) (reduction I x' e ≫ pGl U e) z JM *
          (val (DVR.tG U e α) (reduction I x' e) z JM).val =
          gs (adicLevelι J (e + 1)) z ⊤ (c α) * (val g (adicLevelι J (e + 1)) z JM ^ k).val := fun α _ => by
        rw [hy₃ α z JM hJM, hy₂]; exact hc α _ _ z JM hJM
      rw [hsv, h1 _ _ z JL hJL, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hwv, hw, mul_pow,
        Units.val_mul] at hE
      have hfin : gs (adicLevelι J (e + 1)) z ⊤ a = ∑ α ∈ S, gs (adicLevelι J (e + 1)) z ⊤ (c α) := by
        refine (Units.mul_left_inj (wVal U e z JM JL (reduction I x' e) ^ k *
          val g' (adicLevelι J (e + 1)) z JL ^ k)).1 ?_
        rw [Units.val_mul]
        linear_combination hE
      have gsub : ∀ x y : Γ(Sp W, ⊤), gs (adicLevelι J (e + 1)) z ⊤ (x - y) =
          gs (adicLevelι J (e + 1)) z ⊤ x - gs (adicLevelι J (e + 1)) z ⊤ y := fun x y => by
        simp only [gs_eq _ z ⊤ trivial, map_sub]
      rw [map_sub, map_sum, toΓ_hom, gsub, DVR.gs_fsum _ z ⊤ trivial, hfin, sub_eq_zero]
      exact Finset.sum_congr rfl fun α _ => by rw [toΓ_hom]

end GlobalTheory.RayEv.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Set GlobalTheory.CxPts GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.ShFam.Hor.Sec

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {A : Set (CxPts p σ)}

theorem eqOn_of_dense (hA : Dense A) {T : Set (CxPts p σ)} (hT : IsOpen T) {f g : CxPts p σ → ℂ}
    (hf : R.HoloOn T f) (hg : R.HoloOn T g) (h : EqOn f g (T ∩ A)) : EqOn f g T :=
  h.of_subset_closure (hf.continuousOn hT) (hg.continuousOn hT) inter_subset_left (hA.open_subset_closure_inter hT)

theorem exists_holoOn_of_local (hA : Dense A) {S : Set (CxPts p σ)} {u : CxPts p σ → ℂ}
    (h : ∀ y ∈ S, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn S f ∧ EqOn f u (S ∩ A) := by
  choose! T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := fun y : S => T y) (fun y => hT y y.2)
    (fun y hS => ⟨⟨y, hS⟩, hy y hS⟩) fun y => ((hf y y.2).mono inter_subset_right).congr fun z hz => ?_,
    fun y hS => he y hS.1 ⟨hy y hS.1, hS.2⟩⟩
  exact eqOn_of_dense hA ((hT z hz.1).inter (hT y y.2)) ((hf z hz.1).mono inter_subset_left)
    ((hf y y.2).mono inter_subset_right)
    (fun w hw => (he z hz.1 ⟨hw.1.1, hw.2⟩).trans (he y y.2 ⟨hw.1.2, hw.2⟩).symm) ⟨hy z hz.1, hz.2⟩

theorem isHolTo_symm (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

variable [IsIntegral Y]

theorem ev_mul_eq {U V W : Y.Opens} {a : Γ(Y, U)} {b : Γ(Y, V)} {c : Γ(Y, W)} {y : CxPts p σ}
    (hU : y ∈ ptsIn p σ U) (hV : y ∈ ptsIn p σ V) (hW : y ∈ ptsIn p σ W)
    (h : ∀ h₁ h₂ h₃, fnOf U h₁ a * fnOf V h₂ b = fnOf W h₃ c) : ev p σ U a y * ev p σ V b y = ev p σ W c y := by
  have hy : y ∈ ptsIn p σ (U ⊓ V ⊓ W) := mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hU, hV⟩, hW⟩
  rw [← ev_res (inf_le_left.trans inf_le_left) hy, ← ev_res (inf_le_left.trans inf_le_right) hy,
    ← ev_res inf_le_right hy, ← ev_mul]
  congr 1
  exact fn_ext fun _ => by rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, h]

theorem holSec_ne_bot [Nonempty (CxPts p σ)] (hA : Dense A) (D : CartierDiv Y) (W : Y → Y.Opens)
    (δ : Y → Y.functionFieldˣ) (hW : ∀ y, y ∈ W y) (hδ : ∀ y, ∀ y' ∈ W y, D.IsEqn y' (δ y))
    (u : Y → CxPts p σ → ℂ) (hu : ∀ y, R.HoloOn (ptsIn p σ (W y)) (u y))
    (h0 : ∀ y, ∀ z ∈ ptsIn p σ (W y) ∩ A, u y z ≠ 0)
    (hc : ∀ y y' (r : Γ(Y, W y ⊓ W y')), (∀ h, fnOf _ h r = (δ y : Y.functionField) / (δ y' : Y.functionField)) →
      ∀ z ∈ ptsIn p σ (W y ⊓ W y') ∩ A, u y z = ev p σ _ r z * u y' z) :
    R.holSec (toLB D) ≠ ⊥ := by
  choose r hr using fun (i : (toLB D).ι) (y : Y) => exists_unit_fnOf_eq (U := (toLB D).U i ⊓ W y)
    (f := (i.1.2 : Y.functionField) / (δ y : Y.functionField))
    fun x hx => (hδ y x hx.2).iff_unitAt.1 (i.2.2 x hx.1)
  let pt (z : CxPts p σ) : Y := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : CxPts p σ) : z ∈ ptsIn p σ (W (pt z)) := mem_ptsIn.2 (hW _)
  let s (i : (toLB D).ι) (z : CxPts p σ) : ℂ := ev p σ _ (r i (pt z)).val z * u (pt z) z
  have key {i y z} (hi : z ∈ ptsIn p σ ((toLB D).U i)) (hy : z ∈ ptsIn p σ (W y)) :
      s i z = ev p σ _ (r i y).val z * u y z := by
    obtain ⟨t, ht⟩ := exists_unit_fnOf_eq (U := W (pt z) ⊓ W y)
      (f := (δ (pt z) : Y.functionField) / (δ y : Y.functionField))
      fun x hx => (hδ y x hx.2).iff_unitAt.1 (hδ _ x hx.1)
    have hz := mem_ptsIn_inf.2 ⟨hpt z, hy⟩
    have e : u (pt z) z = ev p σ _ t.val z * u y z :=
      eqOn_of_dense (R := R) hA (isOpen_ptsIn _) ((hu _).mono (ptsIn_mono inf_le_left))
        ((R.holoOn_ev _ t.val).mul ((hu y).mono (ptsIn_mono inf_le_right))) (hc _ _ _ ht) hz
    rw [← ev_mul_eq (a := (r i (pt z)).val) (b := t.val) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩) hz (mem_ptsIn_inf.2 ⟨hi, hy⟩)
      fun _ _ _ => by rw [hr, hr, ht, div_mul_div_cancel₀ (Units.ne_zero _)], _root_.mul_assoc, ← e]
  have hs : s ∈ R.holSec (toLB D) := by
    refine ⟨⟨fun i j z hi hj => ?_, fun i z hi => ?_⟩, fun i => ?_⟩
    · have e := ev_mul_eq (a := ((toLB D).g i j).val) (b := (r j (pt z)).val) (c := (r i (pt z)).val)
        (mem_ptsIn_inf.2 ⟨hi, hj⟩) (mem_ptsIn_inf.2 ⟨hj, hpt z⟩) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩)
        fun _ _ _ => by rw [hr, hr, fnOf_toLB_g, div_mul_div_cancel₀ (Units.ne_zero _)]
      simp only [s]
      rw [← e, _root_.mul_assoc]
      rfl
    · simp only [s]
      rw [ev_of_notMem (fun h => hi (mem_ptsIn_inf.1 h).1), zero_mul]
    · exact AnRead.holoOn_of_cover (T := fun y => ptsIn p σ (W y)) (fun y => isOpen_ptsIn _)
        (fun z _ => ⟨_, hpt z⟩) fun y =>
        ((AnRead.holoOn_ev_of_subset (r i y).val fun _ => mem_ptsIn_inf.2).mul
          ((hu y).mono inter_subset_right)).congr fun z hz => key hz.1 hz.2
  obtain ⟨z, hz⟩ := hA.nonempty
  intro hb
  rw [hb, Submodule.mem_bot] at hs
  let i : (toLB D).ι := ⟨(W (pt z), δ (pt z)), gen_mem (hW _), hδ _⟩
  exact mul_ne_zero (ev_ne_zero (mem_ptsIn_inf.2 ⟨hpt z, hpt z⟩) (r i (pt z)).isUnit) (h0 _ z ⟨hpt z, hz⟩)
    (congrFun (congrFun hs i) z)

end General

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem logGrowth_inv {h : CxFr Z σ → ℂ} (hg : LogGrowth h) : LogGrowth fun a => (h a)⁻¹ := fun x₀ => by
  obtain ⟨N, φ, h₁, h₂, h₃, h₄, h₅⟩ := hg x₀
  refine ⟨N, φ, h₁, h₂, h₃, h₄, fun V _ _ _ B a hB ha hN b₀ hb => ?_⟩
  obtain ⟨C, k, hk⟩ := h₅ V B a hB ha hN b₀ hb
  exact ⟨C, k, hk.mono fun b hb hi => ⟨(hb hi).2, by rw [inv_inv]; exact (hb hi).1⟩⟩

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ' : k →+* ℂ} {d : ℕ}

theorem inner_iff {π : Y ⟶ gen Z} {z : CxPts p σ'} {x : CxPts (genStr Z) σ} (h : x.1 = z.1 ≫ π) :
    Inner x ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) := by
  rw [Inner, h, mem_ptsIn]
  rfl

theorem exists_extension (R : AnRead p σ' d) (π : Y ⟶ gen Z)
    (hA : Dense (ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl))) {S : Set (CxPts p σ')} (hS : IsOpen S)
    {a : CxPts p σ' → CxFr Z σ} (ha : ∀ z ∈ S, (a z).1.1 = z.1 ≫ π)
    (hf : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (x : V → CxPts p σ'), IsOpen B → IsHolTo B (fun b => (x b).1) → MapsTo x B S → HolFam B fun b => a (x b))
    {h : CxFr Z σ → ℂ}
    (hh : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B)
    (hg : LogGrowth h) :
    ∃ f, R.HoloOn S f ∧ EqOn f (fun z => h (a z)) (S ∩ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl)) := by
  refine exists_holoOn_of_local hA fun y hy => ?_
  obtain ⟨N, φ, hN, hyN, hφ, hφ0, hgr⟩ := hg (a y).1
  obtain ⟨N', hN', rfl⟩ := isOpen_induced_iff.1 hN
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let T : Set (CxPts p σ') := S ∩ (fun z => z.1 ≫ π) ⁻¹' N'
  have hT : IsOpen T := hS.inter (hN'.preimage ((Points.continuous_comp π).comp continuous_subtype_val))
  have hTN (z) (hz : z ∈ T) : (a z).1 ∈ Subtype.val ⁻¹' N' := by
    rw [mem_preimage, ha z hz.1]; exact hz.2
  have hyT : y ∈ T := ⟨hy, by rw [mem_preimage, ← ha y hy]; exact hyN⟩
  let B := c.e.target ∩ c.e.symm ⁻¹' T
  have hB : IsOpen B := ChartGlue.isOpen_over c.e hT
  have hfam {B' : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB' : IsOpen B') (e : B' ⊆ B) : HolFam B' fun b => a (c.e.symm b) :=
    hf _ B' c.e.symm hB' (isHolTo_symm c hB' (e.trans inter_subset_left)) fun b hb => (e hb).2.1
  have hφB : DifferentiableOn ℂ (fun b => φ (a (c.e.symm b)).1) B :=
    hφ _ B (fun b => (a (c.e.symm b)).1) hB (hfam hB subset_rfl).1 fun b hb => hTN _ hb.2
  have hin (z) (hz : z ∈ T) : φ (a z).1 ≠ 0 ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) :=
    (hφ0 _ (hTN z hz)).trans (inner_iff (ha z hz.1))
  have hB' : IsOpen {b ∈ B | φ (a (c.e.symm b)).1 ≠ 0} :=
    hφB.continuousOn.isOpen_inter_preimage hB isOpen_ne
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.riemann_extension_of_log_growth _ B _ (fun b => h (a (c.e.symm b))) hB hφB
    (hh _ _ _ hB' (hfam hB' (sep_subset _ _)) fun b hb => (hφ0 _ (hTN _ hb.1.2)).1 hb.2)
    (fun b hb => by
      have hs := c.e.map_target hb.1
      have h₁ := hA.open_subset_closure_inter (c.e.open_source.inter hT) ⟨hs, hb.2⟩
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb.1] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, ?_⟩
      rw [c.e.left_inv hz.1.1]
      exact (hin z hz.1.2).2 hz.2)
    fun b hb => by
      obtain ⟨C, n, hn⟩ := hgr _ B _ hB (hfam hB subset_rfl) (fun b hb => hTN _ hb.2) b hb
      refine ⟨C, n, ?_⟩
      filter_upwards [hn, hB.mem_nhds hb] with b' h₁ h₂ h₃
      exact (h₁ ((hφ0 _ (hTN _ h₂.2)).1 h₃)).1
  refine ⟨c.e.source ∩ T, u ∘ c.e, c.e.open_source.inter hT, ⟨hi, hyT⟩,
    AnRead.holoOn_of_chart c (hu.congr fun b hb => congrArg u (c.e.right_inv hb.1)), fun z hz => ?_⟩
  have := he (x := c.e z) ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, by
    rw [c.e.left_inv hz.1.1]; exact (hin z hz.1.2).2 hz.2⟩
  simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this

end Flag

theorem H0_ne_bot_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ) (h : CxFr Z σ → ℂ), τ (H.rt : E) = H.rt0 → HorFn τ h → (C.Y.H0 (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥ ∧ C.Y.H0 (-divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ _ e C τ h hτ hh
  obtain ⟨W, δ, a, hW, hδ, ha, hf, hc⟩ := GlobalTheory.T.exists_local_equation_complex_points E H Dw l Xo c O β Z σ F e C τ hτ
  obtain ⟨hne, hd⟩ := GlobalTheory.T.complexPoints_nonempty_dense_variety F C.Y (σ.comp e.toRingHom)
  have hA := hd (C.π ⁻¹ᵁ (genBd Z).compl) ⟨genericPt C.Y (IsLocalRing.closedPoint C.Y.Fn), fun hb =>
    hb ⟨_, congrArg (fun g => g (IsLocalRing.closedPoint C.Y.Fn)) C.y0_x⟩⟩
  let R := AnRead.all C.Y.str (σ.comp e.toRingHom) C.Y.dim
  choose u hu he using fun y => exists_extension R C.π hA (isOpen_ptsIn (W y)) (ha y) (hf y) hh.2.2.1 hh.2.2.2
  choose u' hu' he' using fun y => exists_extension R C.π hA (isOpen_ptsIn (W y)) (ha y) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  have h0 (y) (z) (hz : z ∈ ptsIn _ _ (W y) ∩ ptsIn _ _ (C.π ⁻¹ᵁ (genBd Z).compl)) : h (a y z) ≠ 0 :=
    hh.1 _ ((inner_iff (ha y z hz.1)).2 hz.2)
  have hr (y y') (U : C.Y.X.Opens) (r : Γ(C.Y.X, U)) (hr : ∀ hU, fnOf U hU r = (δ y : C.Y.Fn) / (δ y' : C.Y.Fn)) (z)
      (hy : z ∈ ptsIn _ _ (W y)) (hy' : z ∈ ptsIn _ _ (W y')) (hU : z ∈ ptsIn _ _ U)
      (hz : z ∈ ptsIn _ _ (C.π ⁻¹ᵁ (genBd Z).compl)) : h (a y z) = ev _ _ U r z * h (a y' z) := by
    obtain ⟨M, N, hM, hN, hM0, hMN⟩ := hc y y' U (gen_mem (mem_ptsIn.1 hU)) r (hr _) z
      (mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hy, hy'⟩, hU⟩)
    refine mul_right_cancel₀ hM0 ?_
    rw [hh.2.1 _ _ M N ((inner_iff (ha y' z hy')).2 hz) hM hN, ← hMN]
    ring
  refine ⟨GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot F C.Y _ R _ (holSec_ne_bot hA _ W δ hW hδ u hu (fun y z hz => ?_) fun y y' r hr' z hz => ?_),
    GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot F C.Y _ R _ (holSec_ne_bot hA _ W (fun y => (δ y)⁻¹) hW (fun y y' hy => (hδ y y' hy).neg) u' hu'
      (fun y z hz => ?_) fun y y' r hr' z hz => ?_)⟩
  · rw [he y hz]; exact h0 y z hz
  · have hz' := mem_ptsIn_inf.1 hz.1
    rw [he y ⟨hz'.1, hz.2⟩, he y' ⟨hz'.2, hz.2⟩]
    exact hr y y' _ r hr' z hz'.1 hz'.2 hz.1 hz.2
  · rw [he' y hz]; exact inv_ne_zero (h0 y z hz)
  · have hz' := mem_ptsIn_inf.1 hz.1
    have e := hr y' y _ r (fun hU => by
      rw [hr', Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv]) z hz'.2 hz'.1 hz.1 hz.2
    rw [he' y ⟨hz'.1, hz.2⟩, he' y' ⟨hz'.2, hz.2⟩]
    have h₁ := h0 y' z ⟨hz'.2, hz.2⟩
    rw [eq_mul_inv_iff_mul_eq₀ h₁, e, _root_.mul_comm, mul_inv_cancel_right₀ (h0 y z ⟨hz'.1, hz.2⟩)]

end GlobalTheory.ShFam.Hor.Sec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_conj_symm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hH.apply i j
  rw [← this]
  simp only [star_star, Pi.star_apply]
  ring

noncomputable def hermFormImBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem hermForm_periods_alternating_nondeg :
    ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  intro g r x M Hm hli hsp hH hpos hM
  have hanti : Mᵀ = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, ← hM]
    rw [hermForm_conj_symm_of_isHermitian Hm hH]
    simp
  refine ⟨hanti, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z : Fin g → ℂ := ∑ j, v j • x j with hz
    have hz0 : z ≠ 0 := by
      intro h0
      apply hv0
      funext j
      exact Fintype.linearIndependent_iff.mp hli v h0 j
    have hxi : ∀ i, hermFormImBilin Hm (x i) z = 0 := by
      intro i
      have : hermFormImBilin Hm (x i) z = ∑ j, v j * M i j := by
        rw [hz, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, ← hM i j]
        rfl
      rw [this]
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have hall : ∀ y, hermFormImBilin Hm y z = 0 := by
      have hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker ((hermFormImBilin Hm).flip z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa using hxi i
      intro y
      have hy : y ∈ Submodule.span ℝ (Set.range x) := by rw [hsp]; trivial
      simpa using hle hy
    have h1 := hall (Complex.I • z)
    have h2 : hermFormImBilin Hm (Complex.I • z) z = (hermForm Hm z z).re := by
      show (hermForm Hm (Complex.I • z) z).im = _
      simp [hermForm, smul_dotProduct]
    have := hpos z hz0
    linarith
  · have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Module.finrank_pi_fintype] at h1
    simp [Complex.finrank_real_complex] at h1
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InConeOfMonomialMultiple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem inCone_of_isMonomial_smul {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) {m : ℕ} (t : Fin m → R)
    (γ δ : Fin m → LinearMap.BilinForm ℤ Dg.X) (N : ℕ) (_hN : 0 < N) (hγ : ∀ i, γ i = (N : ℤ) • δ i)
    (hs : ∀ i y z, δ i y z = δ i z y) (_hne : ∀ i, δ i ≠ 0) (hm : IsMonomial Dg t γ) : InCone Dg δ := by
  intro W _ _ _ hW ϖ hϖ f be hbe hf
  have hsγ : ∀ i y z, γ i y z = γ i z y := fun i y z => by
    rw [hγ i, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, hs i y z]
  obtain ⟨c, hc, e⟩ := StepCheck.inCone_of_isMonomial hsγ hm W hW ϖ hϖ f be hbe hf
  refine ⟨fun i => c i * N, fun i => mul_nonneg (hc i) N.cast_nonneg, ?_⟩
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a b
  simp [toReal, hγ i, smul_eq_mul, mul_assoc]

end GlobalTheory.GenFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameValuationBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_valuation_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (b : Z.i.c.V W →+* Γ(Z.X, U)), hU.fromSpec ≫ Z.s = spMap b → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (a : 𝓞 E) (h : embK Z.i.c τ a ∈ Z.i.c.V W), w τ i ≫ ((Y Z.i).t.act.act a).left = spMap (epsMul (b ⟨_, h⟩)) ≫ w τ i := by
  first | exact @GlobalTheory.HTLine.eig_of_intFrame | exact GlobalTheory.HTLine.eig_of_intFrame | (intros; apply GlobalTheory.HTLine.eig_of_intFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterSectionOnMapStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letter_section_on_map : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → N2 Y → ∀ (Z Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), IsMap Z' Z f → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ st (x : Letter Dw), letterOf Dw st = some x → ∀ (U : Z.X.Opens) (m m' : ℕ) (A : Fin m → Γ(Z.X, U)) (B : Fin m' → Γ(Z.X, U)), RatioAt Z st U A B → ∀ (U' : Z'.X.Opens) (h : U' ≤ f ⁻¹ᵁ U), RatioAt Z' st U' (fun j => (f.appLE U U' h).hom (A j)) (fun j => (f.appLE U U' h).hom (B j)) := by
  first | exact @GlobalTheory.HTLine.ratioAt_pull | exact GlobalTheory.HTLine.ratioAt_pull | (intros; apply GlobalTheory.HTLine.ratioAt_pull <;> assumption)
end

