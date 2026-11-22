import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameThinAffineBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_map_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val _ (f y) U h, ← Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem isoOn_of_lbIso (X : Scheme.{0}) (W : X.Opens) (L M : LB X) (h : LBIso (L.pull W.ι) (M.pull W.ι)) :
    ∃ w : Cmp W L M, IsoOn W L M w := by
  obtain ⟨s, hs⟩ := h
  have hle : ∀ (a : L.ι) (b : M.ι), W ⊓ (L.U a ⊓ M.U b) ≤
      W.ι ''ᵁ ((M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a)) := by
    intro a b x hx
    obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx.1⟩, rfl⟩
    exact W.ι.apply_mem_image_iff.2 ⟨mem_pull.2 hx.2.2, mem_pull.2 hx.2.1⟩
  refine ⟨fun a b => (res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹, ?_⟩
  intro x hx a a' b b' ha ha' hb hb'
  obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have E : ∀ (a : L.ι) (b : M.ι), W.ι y ∈ L.U a → W.ι y ∈ M.U b →
      gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) =
      (gm (𝟙 _) y _ (s.s (fun _ => b, fun _ => a)))⁻¹ := by
    intro a b ha hb
    have hm : W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) := ⟨hx, ha, hb⟩
    have hv : (𝟙 W.toScheme) y ∈ (M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a) :=
      ⟨mem_pull.2 hb, mem_pull.2 ha⟩
    have e := GlobalTheory.GlueLineBundle.gm_imU W.ι (𝟙 _) y _ hv (s.s (fun _ => b, fun _ => a))
    rw [Category.id_comp] at e
    rw [map_inv, gm_res W.ι y (hle a b) hm, e]
    rfl
  have EL : ∀ (a a' : L.ι), W.ι y ∈ L.U a → W.ι y ∈ L.U a' →
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') = gm (𝟙 _) y _ ((L.pull W.ι).g (fun _ => a) (fun _ => a')) := by
    intro a a' ha ha'
    have e := gm_pull_g L W.ι (𝟙 _) y (fun _ => a) (fun _ => a') (mem_pull.2 ha) (mem_pull.2 ha')
    rw [Category.id_comp] at e
    exact e.symm
  have EM : ∀ (b b' : M.ι), W.ι y ∈ M.U b → W.ι y ∈ M.U b' →
      gm W.ι y (M.U b ⊓ M.U b') (M.g b b') = gm (𝟙 _) y _ ((M.pull W.ι).g (fun _ => b) (fun _ => b')) := by
    intro b b' hb hb'
    have e := gm_pull_g M W.ι (𝟙 _) y (fun _ => b) (fun _ => b') (mem_pull.2 hb) (mem_pull.2 hb')
    rw [Category.id_comp] at e
    exact e.symm
  have hp : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b, fun _ => a) := ⟨mem_pull.2 hb, mem_pull.2 ha⟩
  have hq : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b', fun _ => a') := ⟨mem_pull.2 hb', mem_pull.2 ha'⟩
  have G := (isGen_iff_germ s).1 hs y _ _ hp hq
  rw [gm_div' (M.pull W.ι) (L.pull W.ι) (𝟙 _) y _ _ hp hq] at G
  have alg : ∀ {Gp : Type} [CommGroup Gp] (S Mg large₂ S' : Gp), S = Mg * large₂⁻¹ * S' → S⁻¹ * Mg = large₂ * S'⁻¹ := by
    intro Gp _ S Mg large₂ S' e
    rw [e, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
    exact _root_.mul_comm _ _
  have key : gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) *
        gm W.ι y (M.U b ⊓ M.U b') (M.g b b') =
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') * gm W.ι y (W ⊓ (L.U a' ⊓ M.U b'))
        ((res (hle a' b') (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b', fun _ => a'))))⁻¹) := by
    rw [E a b ha hb, E a' b' ha' hb', EL a a' ha ha', EM b b' hb hb']
    exact alg _ _ _ _ G
  have hinj : Function.Injective (Units.map (W.ι.stalkMap y).hom.toMonoidHom) := fun u v e =>
    Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1 (congrArg Units.val e))
  apply hinj
  rw [map_mul, map_mul, ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) from ⟨hx, ha, hb⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ M.U b ⊓ M.U b' from ⟨hb, hb'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ L.U a ⊓ L.U a' from ⟨ha, ha'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a' ⊓ M.U b') from ⟨hx, ha', hb'⟩)]
  exact key

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPrimeMultOfFiresAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Sinf] [Module ℂ Sinf]
  [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]

theorem exists_isThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by
  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν) ?_ ?_ ?_ ?_, hint,
    fun f e g => rfl⟩
  · intro f f' e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    exact integral_add (hint f e g) (hint f' e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]
    exact integral_smul c _
  · intro f e e'
    funext g
    simp only [Pi.add_apply, map_add, LinearMap.add_apply]
    exact integral_add (hint f e g) (hint f e' g)
  · intro c f e
    funext g
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply]
    exact integral_smul c _

theorem exists_isThetaP' (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 th pt io A thP := by
  obtain rfl : th = fun g h s => thL g h s := funext fun g => funext fun h => funext fun s => h1 g h s
  obtain rfl : pt = fun s => ptL s := funext h2
  exact exists_isThetaP ν 𝓕 thL ptL io A hint

theorem exists_linear_choice {X M N : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (W : Submodule ℂ M) (r : M →ₗ[ℂ] N) (u : X →ₗ[ℂ] N)
    (h : ∀ x, ∃ m ∈ W, r m = u x) : ∃ y : X →ₗ[ℂ] M, (∀ x, y x ∈ W) ∧ ∀ x, r (y x) = u x := by
  choose m hm hr using h
  let b := Module.Basis.ofVectorSpace ℂ X
  let y' : X →ₗ[ℂ] W := b.constr ℂ fun k => ⟨m (b k), hm _⟩
  refine ⟨W.subtype ∘ₗ y', fun x => (y' x).2, fun x => ?_⟩
  have : r ∘ₗ W.subtype ∘ₗ y' = u := b.ext fun k => by
    simp only [LinearMap.comp_apply, y', Module.Basis.constr_basis, Submodule.subtype_apply, hr]
  exact LinearMap.congr_fun this x

theorem exists_linear_lift {ι X : Type} [AddCommGroup X] [Module ℂ X] {M : ι → Type} [∀ a, AddCommGroup (M a)]
    [∀ a, Module ℂ (M a)] (low : ∀ a, Submodule ℂ (M a)) (W : Submodule ℂ (MultilinearMap ℂ M (G' → ℂ)))
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : (⨂[ℂ] a, low a) →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (ext : X →ₗ[ℂ] (H' → Tau))
    (h : ∀ x, (∀ e g, IntegrableOn (fun h => th g h (pt (io e (ext x h)))) 𝓕 ν) ∧
      ∃ U ∈ W, ∀ v : ∀ a, low a, U (fun a => (v a : M a)) = Lift.thetaPInt ν 𝓕 th pt io (ext x) (PiTensorProduct.tprod ℂ v)) :
    ∃ y : X →ₗ[ℂ] MultilinearMap ℂ M (G' → ℂ), (∀ x, y x ∈ W) ∧
      ∃ thP : LinearMap.range ext →ₗ[ℂ] ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)),
        Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range ext) thP ∧
          ∀ (x : X) (v : ∀ a, low a), y x (fun a => (v a : M a)) = thP (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) := by
  obtain ⟨thP, hP⟩ := exists_isThetaP' ν 𝓕 th pt thL ptL h1 h2 io (LinearMap.range ext) (by
    rintro ⟨_, x, rfl⟩ e g
    exact (h x).1 e g)
  let r : MultilinearMap ℂ M (G' → ℂ) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U fun a => (v a : M a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U (PiTensorProduct.tprod ℂ v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨y, hy, hr⟩ := exists_linear_choice W r (p ∘ₗ thP ∘ₗ ext.rangeRestrict) fun x => by
    obtain ⟨U, hU, hv⟩ := (h x).2
    exact ⟨U, hU, funext fun v => funext fun g =>
      (congrFun (hv v) g).trans (hP.eq (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) g).symm⟩
  exact ⟨y, hy, thP, hP, fun x v => congrFun (hr x) v⟩

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring GlobalTheory.IndefiniteRowSideFullHecke.ThetaPrimeMultiplicity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernelL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : WO (Vc D i) (Wc D i) => ℂ) 0 ∘ₗ R.ωP i t (h, g)

end GlobalTheory.ThetaFiresLinear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoBaseChangesOfCongruentMapsPureHodge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTower

open ReciprocityTheory.ChartRestriction.G.Out (thick thickTrans thickObj thickMap thickTrans_comp)

theorem exists_end {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : G' ⟶ G', IsMonHom U ∧ U.left ≫ φ = φ ≫ W.left := by
  let U : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ W.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have e : U.left ≫ φ = φ ≫ W.left := h.1.lift_fst _ _ _
  exact ⟨U, Out.PullGtPf.isMonHom_of_grpPullback h h W U e, e⟩

variable {T : Type} [CommRing T] (I : Ideal T)

theorem thickMap_fst (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ pullback.fst A.hom (thick T I (e + 1)) = pullback.fst A.hom (thick T I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_hom (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ (thickObj T I (e + 1) A).hom = (thickObj T I e A).hom ≫ thickTrans T I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap (e : ℕ) (A : Over (Sp T)) [GrpObj A] :
    IsGrpPullback (thickObj T I e A) (thickObj T I (e + 1) A) (thickTrans T I e) (thickMap T I e A) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (thickTrans_comp T I e).symm (thickMap_fst I e A).symm) (thickMap_hom I e A)

theorem ker_factor_sq (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2
      = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ]
  exact Ideal.mul_mem_mul hx (Ideal.pow_le_self (Nat.succ_ne_zero e) hy)

variable {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G]

theorem isGrpPullback_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (e : ℕ) :
    IsGrpPullback (thickObj T I e A) G (spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp a))
      (pullback.fst A.hom (thick T I e) ≫ φ) :=
  ((isGrpPullback_pullback A _).comp h).congr (by rw [← Spec.map_comp]; rfl) rfl

theorem exists_end_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : ∀ e, thickObj T I e A ⟶ thickObj T I e A, (∀ e, IsMonHom (U e)) ∧
      (∀ e, (U e).left ≫ pullback.fst A.hom (thick T I e) ≫ φ = (pullback.fst A.hom (thick T I e) ≫ φ) ≫ W.left) ∧
      ∀ e, thickMap T I e A ≫ (U (e + 1)).left = (U e).left ≫ thickMap T I e A := by
  choose U hU eU using fun e => exists_end (isGrpPullback_red I h e) W
  refine ⟨U, hU, eU, fun e => (isGrpPullback_red I h (e + 1)).1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, eU, Category.assoc (U e).left, ← Category.assoc (thickMap T I e A),
      ← Category.assoc (thickMap T I e A), thickMap_fst, eU]
  · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, ← Category.assoc, Over.w]

theorem existsUnique_hom (hF : GlobalTheory.Published.FormalAlgebraisation) (hM : GlobalTheory.Published.GrothendieckMessing) {g : ℕ}
    (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) (W : G ⟶ G) [IsMonHom W] {r s : S}
    (hW : IsPureBC G W r s) [IsNoetherianRing T] (hI : IsAdicComplete I T) {p : ℕ} (hp : p.Prime) (hpI : (p : T) ∈ I)
    {a b : S →+* T} (hab : ∀ x, a x - b x ∈ I) (hu : IsUnit (a r - b s)) {A B : Over (Sp T)} [GrpObj A] [GrpObj B]
    {φ : A.left ⟶ G.left} {ψ : B.left ⟶ G.left} (hA : IsGrpPullback A G (spMap a) φ)
    (hB : IsGrpPullback B G (spMap b) ψ) :
    ∃! F : A ⟶ B, IsMonHom F ∧ ∀ (X : Scheme.{0}) (x : X ⟶ A.left) (t : X ⟶ Sp (T ⧸ I ^ (0 + 1))),
      x ≫ A.hom = t ≫ thick T I 0 → x ≫ F.left ≫ ψ = x ≫ φ := by
  obtain ⟨U, hU, eU, cU⟩ := exists_end_red I hA W
  obtain ⟨V, hV, eV, cV⟩ := exists_end_red I hB W
  have rA := isGrpPullback_red I hA
  have rB := isGrpPullback_red I hB
  have e0 : (Ideal.Quotient.mk (I ^ (0 + 1))).comp a = (Ideal.Quotient.mk (I ^ (0 + 1))).comp b :=
    RingHom.ext fun x => Ideal.Quotient.eq.2 (by simpa using hab x)
  obtain ⟨f₀, hf₀, ef₀⟩ := grpPullback_iso (rA 0) ((rB 0).congr (by rw [e0]) rfl)
  let P : ℕ → Type := fun e => {f : thickObj T I e A ⟶ thickObj T I e B // IsMonHom f ∧ U e ≫ f = f ≫ V e}
  have step : ∀ (e : ℕ) (f : P e), ∃ f' : P (e + 1), thickMap T I e A ≫ f'.1.left = f.1.left ≫ thickMap T I e B ∧
      ∀ k : thickObj T I (e + 1) A ⟶ thickObj T I (e + 1) B, IsMonHom k →
        thickMap T I e A ≫ k.left = f.1.left ≫ thickMap T I e B → k = f'.1 := by
    intro e f
    have := f.2.1
    obtain ⟨k, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.pure_endomorphism_hom_lift_square_zero hM p hp _ _
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))
      ⟨e + 1 + 1, by
        rw [← map_natCast (Ideal.Quotient.mk (I ^ (e + 1 + 1))), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hpI _⟩
      (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) g g _ _ _ _ _ _
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rA (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rA (e + 1)).1 hg)
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rB (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rB (e + 1)).1 hg)
      (isGrpPullback_thickMap I e A) (isGrpPullback_thickMap I e B) (U (e + 1)) (V (e + 1)) (U e) (V e) (cU e) (cV e)
      _ _ _ _ (hW _ _ _ _ (rA (e + 1)) _ (eU _)) (hW _ _ _ _ (rB (e + 1)) _ (eV _))
      (by simpa using hu.map (Ideal.Quotient.mk (I ^ (e + 1 + 1)))) f.1 f.2.2
    exact ⟨⟨k, h₁, h₃⟩, h₂, h₄⟩
  choose nx h₁ h₂ using step
  have c₀ : U 0 ≫ f₀.hom = f₀.hom ≫ V 0 := Over.OverMorphism.ext ((rB 0).1.hom_ext
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, ef₀, eU, eV, ← Category.assoc f₀.hom.left,
      ef₀]) (by rw [Over.w, Over.w]))
  let f : ∀ e, P e := fun e => Nat.rec ⟨f₀.hom, hf₀, c₀⟩ nx e
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := GlobalTheory.grpHom_algebraise hF.1 T I hI A B
    (PolPull.isAbelianScheme_of_isGrpPullback hG hA).proper (PolPull.isAbelianScheme_of_isGrpPullback hG hB).proper
    (fun e => thickObj T I e A) (fun e => thickObj T I e B) (fun e => thickMap T I e A) (fun e => thickMap T I e B)
    _ _ (fun e => isGrpPullback_pullback A _) (fun e => thickMap_fst I e A) (fun e => isGrpPullback_pullback B _)
    (fun e => thickMap_fst I e B) (fun e => (f e).1) (fun e => (f e).2.1) (fun e => h₁ e (f e))
  refine ⟨F, ⟨hF₁, fun X x t ht => ?_⟩, fun K ⟨hK, eK⟩ => hF₃ K fun e => ?_⟩
  · have h0 : pullback.fst A.hom (thick T I 0) ≫ F.left = f₀.hom.left ≫ pullback.fst B.hom (thick T I 0) := hF₂ 0
    rw [← pullback.lift_fst x t ht, Category.assoc, Category.assoc, ← Category.assoc _ F.left, h0, Category.assoc, ef₀]
  · have n : ∀ e, ((Over.pullback (thick T I e)).map K).left ≫ pullback.fst B.hom (thick T I e) =
        pullback.fst A.hom (thick T I e) ≫ K.left := fun e => pullback.lift_fst _ _ _
    have key : ∀ e, (Over.pullback (thick T I e)).map K = (f e).1 := by
      intro e
      induction e with
      | zero =>
        refine Over.OverMorphism.ext ((rB 0).1.hom_ext ?_ (by rw [Over.w, Over.w]))
        rw [← Category.assoc, n, Category.assoc, eK _ _ _ pullback.condition]
        exact ef₀.symm
      | succ e ih =>
        refine h₂ e (f e) _ inferInstance ?_
        rw [← ih]
        refine (isGrpPullback_pullback B (thick T I (e + 1))).1.hom_ext ?_ ?_
        · rw [Category.assoc, n, ← Category.assoc, thickMap_fst, Category.assoc, thickMap_fst, n]
        · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, thickMap_hom, ← Category.assoc, Over.w]
    rw [← key, n]

theorem exists_isGrpPullback_of_congr : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (S : Type) [CommRing S] (G : Over (Sp S)) [GrpObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (W : G ⟶ G) [IsMonHom W] (r s : S), IsPureBC G W r s → ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (IsLocalRing.maximalIdeal T) T → ∀ p : ℕ, p.Prime → (p : T) ∈ IsLocalRing.maximalIdeal T → ∀ a b : S →+* T, (∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T) → IsUnit (a (r - s)) → ∀ (A : Over (Sp T)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G (spMap a) φ → ∃ φ' : A.left ⟶ G.left, IsGrpPullback A G (spMap b) φ' ∧ ∀ x : Sp (IsLocalRing.ResidueField T) ⟶ A.left, x ≫ A.hom = spMap (IsLocalRing.residue T) → x ≫ φ = x ≫ φ' := by
  intro hF hM S _ G _ g hG hg W _ r s hW T _ _ _ hI p hp hpI a b hab hu A _ φ hA
  have hB := isGrpPullback_pullback G (spMap b)
  have hba : ∀ x, b x - a x ∈ IsLocalRing.maximalIdeal T := fun x => by
    simpa using neg_mem (hab x)
  have un : ∀ y z : T, IsUnit y → z ∈ IsLocalRing.maximalIdeal T → IsUnit (y + z) := fun y z hy hz => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal y).1
      (by simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).2 h) hz) hy
  rw [map_sub] at hu
  have u₁ : IsUnit (a r - b s) := by simpa using un _ _ hu (hab s)
  have u₂ : IsUnit (b r - a s) := by
    have := un _ _ hu (hba r)
    rwa [add_comm, sub_add_sub_cancel] at this
  have u₃ : IsUnit (b r - b s) := by simpa using un _ _ u₂ (hab s)
  obtain ⟨F, ⟨hF₁, hF₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hab u₁ hA hB
  obtain ⟨K, ⟨hK₁, hK₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hba u₂ hB hA
  have FK : F ≫ K = 𝟙 A := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) hu hA hA).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hK₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hF₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  have KF : K ≫ F = 𝟙 _ := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) u₃ hB hB).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hF₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hK₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  refine ⟨F.left ≫ _, ((isGrpPullback_of_iso ⟨F, K, FK, KF⟩).comp hB).congr (Category.id_comp _) rfl,
    fun x hx => (hF₂ _ x (spMap (Ideal.Quotient.lift _ (IsLocalRing.residue T) fun y hy =>
      (IsLocalRing.residue_eq_zero_iff y).2 (by simpa using hy))) ?_).symm⟩
  rw [hx, ← Spec.map_comp]
  rfl

end GlobalTheory.PureTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameThinAffineBasisStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∃ (C : Type) (_ : Category.{0} C) (_ : Quiver.IsThin C) (G : C ⥤ AffOp X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, opOf G T')ˣ), IsBas (opOf G) ∧ IsFrame L (opOf G) (opOf_le G) u := by
  first | exact @GlobalTheory.LBFrameEx.exists_frame | exact GlobalTheory.LBFrameEx.exists_frame | (intros; apply GlobalTheory.LBFrameEx.exists_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetract
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

theorem germ_pull_eq_stalkMap {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val f y U h, gm_val (𝟙 X) (f y) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

theorem retract_section_apply {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (y : Y) : p (e y) = y := by
  have := congrArg (fun f : Y ⟶ Y ↦ f y) hep
  simpa using this

theorem norm_glue_comm {G : Type} [CommGroup G] (A B F G' R R' : G) (k : A * G' = F * B) :
    A * (G' * R') * (F * R)⁻¹ = B * R' * R⁻¹ := by
  rw [← _root_.mul_assoc, k, mul_inv]
  simp only [_root_.mul_assoc]
  rw [mul_left_comm F, mul_left_comm F, mul_inv_cancel_left]

theorem norm_match_comm {G : Type} [CommGroup G] (A S R R' : G) (h : S = A * R' * R⁻¹) :
    A * S⁻¹ * R' = R := by
  rw [h]; simp only [mul_inv]; simp [mul_comm, mul_left_comm, _root_.mul_assoc]

theorem exists_norm (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (V : Y.Opens)
    (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M)
    (hL : IsOn W₁ L) (hM : IsOn W₂ M) (h₁ : p ⁻¹ᵁ V ≤ W₁) (h₂ : p ⁻¹ᵁ V ≤ W₂)
    (hw : IsoOn (p ⁻¹ᵁ V) L M w) (hr : RigOn e L r) (hr' : RigOn e M r') :
    ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  have hpt := retract_section_apply p e hep
  let O : L.ι × M.ι → Y.Opens := fun i ↦ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2))
  have hOV : ∀ i, O i ≤ V := fun i y hy ↦ by
    have : p (e y) ∈ V := hy.1
    rwa [hpt] at this
  have hOa : ∀ i, O i ≤ e ⁻¹ᵁ L.U i.1 := fun i y hy ↦ hy.2.1
  have hOb : ∀ i, O i ≤ e ⁻¹ᵁ M.U i.2 := fun i y hy ↦ hy.2.2
  have hcov : V ≤ iSup O := fun y hy ↦ by
    have hx : e y ∈ p ⁻¹ᵁ V := show p (e y) ∈ V by rwa [hpt]
    obtain ⟨a, ha⟩ := hL.cov _ (h₁ hx)
    obtain ⟨b, hb⟩ := hM.cov _ (h₂ hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), ⟨hx, ha, hb⟩⟩
  let u : ∀ i, Γ(Y, O i)ˣ := fun i ↦
    pullU e _ (w i.1 i.2) * res (hOb i) (r' i.2) * (res (hOa i) (r i.1))⁻¹
  have hu : ∀ i, ∀ y ∈ O i, gm (𝟙 Y) y (O i) (u i) =
      gm e y _ (w i.1 i.2) * gm (𝟙 Y) y _ (r' i.2) * (gm (𝟙 Y) y _ (r i.1))⁻¹ := by
    intro i y hy
    simp only [u, map_mul, map_inv]
    rw [gm_res (𝟙 Y) y (hOb i) hy, gm_res (𝟙 Y) y (hOa i) hy, gm_pull (𝟙 Y) e y _ hy, Category.id_comp]
  obtain ⟨s, hs⟩ := glue_unit V O hOV hcov u (by
    intro i j y hy
    rw [hu i y hy.1, hu j y hy.2]
    obtain ⟨⟨hV, ha, hb⟩, -, ha', hb'⟩ := hy
    have k := congrArg (Units.map (e.stalkMap y).hom.toMonoidHom) (hw (e y) hV i.1 j.1 i.2 j.2 ha ha' hb hb')
    simp only [map_mul, ← germ_pull_eq_stalkMap] at k
    rw [← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2)) ⟨hV, ha, hb⟩,
      ← germ_pull_eq_stalkMap e y (M.U i.2 ⊓ M.U j.2) ⟨hb, hb'⟩,
      ← germ_pull_eq_stalkMap e y (L.U i.1 ⊓ L.U j.1) ⟨ha, ha'⟩,
      ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U j.1 ⊓ M.U j.2)) ⟨hV, ha', hb'⟩] at k
    rw [hr y i.1 j.1 ha ha', hr' y i.2 j.2 hb hb']
    exact norm_glue_comm _ _ _ _ _ _ k)
  have hle : ∀ (a : L.ι) (b : M.ι), p ⁻¹ᵁ V ⊓ (L.U a ⊓ M.U b) ≤ p ⁻¹ᵁ V := fun _ _ ↦ inf_le_left
  refine ⟨fun a b ↦ w a b * (res (hle a b) (pullU p V s))⁻¹, ?_, ?_⟩
  · intro x hx a a' b b' ha ha' hb hb'
    simp only [map_mul, map_inv]
    rw [gm_res (𝟙 X) x (hle a b) ⟨hx, ha, hb⟩, gm_res (𝟙 X) x (hle a' b') ⟨hx, ha', hb'⟩]
    have k := hw x hx a a' b b' ha ha' hb hb'
    rw [mul_right_comm, k, _root_.mul_assoc]
  · intro y a b hV ha hb
    simp only [map_mul, map_inv]
    have hy : y ∈ O (a, b) := ⟨hV, ha, hb⟩
    rw [gm_res e y (hle a b) ⟨hV, ha, hb⟩, gm_pull e p y V hV, hep, ← gm_res (𝟙 Y) y (hOV (a, b)) hy, hs,
      hu (a, b) y hy]
    exact norm_match_comm _ _ _ _ rfl

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfStrictCocycleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_of_strict_cocycle : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) → IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 → ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  first | exact @GlobalTheory.LBLift.exists_pic_of_strict_lift | exact GlobalTheory.LBLift.exists_pic_of_strict_lift | (intros; apply GlobalTheory.LBLift.exists_pic_of_strict_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlatStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  first | exact @GlobalTheory.FiniteFlatLocal.exists_finFree_local | exact GlobalTheory.FiniteFlatLocal.exists_finFree_local | (intros; apply GlobalTheory.FiniteFlatLocal.exists_finFree_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMirabolicScalarUnitaryDecompositionArchimeStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  first | exact @GlobalTheory.IwasawaLast.iwasawa_lastRow | exact GlobalTheory.IwasawaLast.iwasawa_lastRow | (intros; apply GlobalTheory.IwasawaLast.iwasawa_lastRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilisStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser : ∀ (D : Formalism.BasicNotions.D7) (N : ℕ) (h : ↥(Formalism.MainNotions.StandardLatticesGL3.GA D N)), ∃ p : ℕ, p.Prime ∧ GlobalTheory.NormSum.IntegralOver D p h := by
  first | exact @GlobalTheory.NormSum.exists_prime_integralOver | exact GlobalTheory.NormSum.exists_prime_integralOver | (intros; apply GlobalTheory.NormSum.exists_prime_integralOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmOfDualCharacterStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiLogarithm_of_dualCharacter : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ χ : G.dual.Tate, ∃ (f : MvPowerSeries (Fin d) F.Q) (w : Fin d → F.B), QL μ' ⊤ f ∧ In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) ∧ In (⊤ : Ideal F.B) (frob p F.s f - (p : F.Q) • f) ∧ (∀ i, lin f i = algebraMap F.B F.Q (w i)) ∧ dlog G χ = ∑ i, F.θ (w i) • c.form i ∧ ∀ t, c.HasPeriod F.θ t f (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  first | exact @GlobalTheory.CharLog.exists_log_char_period | exact GlobalTheory.CharLog.exists_log_char_period | (intros; apply GlobalTheory.CharLog.exists_log_char_period <;> assumption)
end

