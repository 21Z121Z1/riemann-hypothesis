import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.FlagEmb.PlkSpan

theorem indep_of_plk_ne_zero (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : plk u id ≠ 0) : LinearIndependent K u := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  set r := GlobalTheory.FlagEmb.plE N k q
  have hdet : (Matrix.of fun l l' => u l (r l')).det ≠ 0 := hq
  have hA := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  refine LinearIndependent.of_comp (LinearMap.funLeft K K r) ?_
  exact hA

theorem plk_ne_zero_of_indep (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : LinearIndependent K u) : plk u id ≠ 0 := by
  let Q : Matrix (Fin (N + 1)) (Fin k) K := (Matrix.of u).transpose
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h0 : Q.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : ∑ l, (x - y) l • u l = 0 := by
      funext r
      have := congrFun h0 r
      simp only [Q, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2 := (Fintype.linearIndependent_iff.1 h) _ h1
    funext l
    exact sub_eq_zero.1 (h2 l)
  obtain ⟨Q', hQ'⟩ := GlobalTheory.matrix_exists_left_inverse_of_field Q hinj
  have hCB := GlobalTheory.FlagEmb.CauchyBinet.lform_plk K N k (Fin k) (Fin k) (fun l => Q' l) u id id
  have hM : (Matrix.of fun l l' => ∑ r, (fun l => Q' l) (id l') r * u (id l) r) = (Q' * Q).transpose := by
    ext l l'
    simp [Q, Matrix.mul_apply, mul_comm]
  rw [hM, hQ', Matrix.transpose_one, Matrix.det_one] at hCB
  intro h0
  rw [h0] at hCB
  simp at hCB

theorem plk_comb (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K) (T : Matrix (Fin k) (Fin k) K) :
    plk (fun l => ∑ j, T l j • u j) id = T.det • plk u id := by
  funext q
  simp only [plk, id, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_mul]
  congr 1
  ext l l'
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem main : ∀ (K : Type) [Field K] (N k : ℕ) (u u' : Fin k → Fin (N + 1) → K), (plk u id ≠ 0 ↔ LinearIndependent K u) ∧ (LinearIndependent K u → ((LinearIndependent K u' ∧ Submodule.span K (Set.range u') = Submodule.span K (Set.range u)) ↔ ∃ r : Kˣ, plk u' id = (r : K) • plk u id)) := by
  intro K _ N k u u'
  refine ⟨⟨indep_of_plk_ne_zero K N k u, plk_ne_zero_of_indep K N k u⟩, fun hu => ⟨?_, ?_⟩⟩
  · rintro ⟨hu', hs⟩
    choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun K).1
      (hs ▸ Submodule.subset_span ⟨l, rfl⟩ : u' l ∈ Submodule.span K (Set.range u))
    have h1 := plk_comb K N k u (Matrix.of c)
    have h2 : (fun l => ∑ j, (Matrix.of c) l j • u j) = u' := funext hc
    rw [h2] at h1
    have hd : (Matrix.of c).det ≠ 0 := by
      intro h0
      exact plk_ne_zero_of_indep K N k u' hu' (by rw [h1, h0, zero_smul])
    exact ⟨Units.mk0 _ hd, h1⟩
  · rintro ⟨r, hr⟩
    have h0 := plk_ne_zero_of_indep K N k u hu
    have h0' : plk u' id ≠ 0 := by
      rw [hr]
      exact smul_ne_zero r.ne_zero h0
    have hr' : plk u id = (r : K)⁻¹ • plk u' id := by
      rw [hr, smul_smul, inv_mul_cancel₀ r.ne_zero, one_smul]
    refine ⟨indep_of_plk_ne_zero K N k u' h0', le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u u' _ h0' hr l
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u' u _ h0 hr' l

end GlobalTheory.FlagEmb.PlkSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.FiniteStable

namespace GlobalTheory.TraitOrder

theorem idlAlong_eq_map {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
  have hx : χ (closedPoint R) ∈ U.1 := hle trivial
  unfold idlAlong
  rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

theorem idlAlong_comp {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
  rw [idlAlong_eq_map J χ ⟨U, hU⟩ hle, idlAlong_eq_map J _ ⟨U, hU⟩ hle', Ideal.map_map]
  congr 1
  have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
  rfl

theorem map_injective {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] {I J : Ideal R}
    (h : I.map f = J.map f) : I = J := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) J]
  exact congrArg _ h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twistOAct (σ : 𝓞 E ≃+* 𝓞 E) {S : Scheme.{0}} {A : PolAV S} (o : letI := H.starRing; A.OAct (𝓞 E)) :
    letI := H.starRing; A.OAct (𝓞 E) :=
  letI := H.starRing
  { act := fun a => o.act (σ a)
    hom := fun a => o.hom _
    map_one := by rw [_root_.map_one, o.map_one]
    map_mul := fun a b => by rw [_root_.map_mul, o.map_mul]
    map_add := fun a b => by rw [_root_.map_add, o.map_add]
    rosati := fun a => by
      have := o.rosati (σ a)
      change RosatiAdj _ _ _ (o.act (H.bar _)) at this
      rwa [← aut_bar] at this }

def twistUnif (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {t : SAB H (Sp R)} (P : PELUnif I t) : PELUnif I (FiniteStable.twist σ hσ t) :=
  letI := H.starRing
  @PELUnif.mk E _ _ _ H R _ _ I (FiniteStable.twist σ hσ t) P.D (Module.compHom _ σ.toRingHom)
    (@DegPre.OAct.mk R _ _ (𝓞 E) _ _ P.D.toPre (Module.compHom _ σ.toRingHom) (twistOAct σ P.oD.onB)
      (fun a y => P.oD.c_lin (σ a) y) (fun a => by
        have := P.oD.tau_bal (σ a)
        change DegPre.TauBal _ _ (P.oD.onB.act (H.bar _)) _ (fun y => H.bar _ • y) at this
        rw [← aut_bar] at this
        exact this))
    P.A (twistOAct σ P.oA) P.U P.bundle
    (@UnifPre.OLinear.mk R _ _ I (𝓞 E) _ _ P.D (Module.compHom _ σ.toRingHom) _ _ _ _ _ _ _ _
      (fun a => P.lin.ext (σ a)) (fun e a => P.lin.q_lin e (σ a)) (fun e a => by
        have := P.lin.i_lin e (σ a)
        change ∃ _, TorusEndOf _ (fun y => H.bar _ • y) _ ∧ _ at this
        rw [← aut_bar] at this
        exact this))
    (by
      have := P.w0
      rw [← hσ] at this
      exact this)

theorem evalZ_twist {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {X : Type}
    [AddCommGroup X] [m : Module (𝓞 E) X] [hf : Module.Finite (𝓞 E) X]
    (hf' : @Module.Finite (𝓞 E) X _ _ (Module.compHom _ σ.toRingHom)) (be : LinearMap.BilinForm ℤ X) :
    @InvFun.evalZ _ _ φ X _ (Module.compHom _ σ.toRingHom) hf' be = φ.evalZ be := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  unfold InvFun.evalZ
  rw [φ.eval_eq hr, ← hφ σ hσ]
  let g : (Fin n → 𝓞 E) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => σ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = σ c • g a := fun c a => by
    change r _ = σ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ.symm (a i), funext fun i => σ.apply_symm_apply _⟩
  letI : Module (𝓞 E) X := Module.compHom _ σ.toRingHom
  exact φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (m' : SABMap t'' t' g) : Nonempty (SABMap t'' t h) :=
  e ▸ ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m').choose⟩

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (n : SABMap t'' t h) : Nonempty (SABMap t'' t' g) := by
  subst e
  exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n).choose⟩

theorem idlAlong_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPhiDiv φ Z BD → IsPhiDiv φ Z' BD' →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Z.X) (χ' : Sp W ⟶ Z'.X)
      (y : Sp (FractionRing W) ⟶ Xo'.XF c'), jK W ≫ χ' = y ≫ Z'.j → jK W ≫ χ = y ≫ r ≫ Z.j →
      idlAlong BD'.idealSheaf χ' = idlAlong BD.idealSheaf χ := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' φ σ r ν _ _ hφ hσ hd hd' W _ _ _ hW χ χ' y hy' hy
  obtain ⟨h₁, h₂, h₃⟩ := hW
  let T : CDVR := { V := W }
  obtain ⟨t', ⟨m'⟩⟩ := exists_pull χ' Z'.t
  obtain ⟨s, ⟨ms⟩⟩ := exists_pull χ (FiniteStable.twist σ hσ Z.t)
  obtain ⟨tK, ⟨mK⟩⟩ := exists_pull y Z'.oF.t
  let ν' : SABMap Z'.oF.t (FiniteStable.twist σ hσ Z.oF.t) r := ⟨ν.cm, ν.cart, ν.base, ν.act, ν.lin⟩
  let mZ : SABMap (FiniteStable.twist σ hσ Z.oF.t) (FiniteStable.twist σ hσ Z.t) Z.j :=
    ⟨Z.m.cm, Z.m.cart, Z.m.base, fun a => Z.m.act (σ a), Z.m.lin⟩
  obtain ⟨a₁⟩ := comp hy'.symm (show SABMap Z'.oF.t Z'.t Z'.j from Z'.m) mK
  obtain ⟨a₂⟩ := cancel rfl m' a₁
  obtain ⟨b₀⟩ := comp rfl mZ ν'
  obtain ⟨b₁⟩ := comp hy.symm b₀ mK
  obtain ⟨b₂⟩ := cancel rfl ms b₁
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H W h₂ t' s tK
    (MorphismProperty.of_isPullback (P := @IsProper) mK.cart.1 Z'.oF.proper) a₂ b₂
  obtain ⟨n⟩ := comp (Category.id_comp χ) ms ψ
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z' m' (jK W) y hy'.symm
  obtain ⟨T', f, u, hi, hl, ⟨mu⟩, ⟨P⟩⟩ := exists_unif_ext T t' hp
  obtain ⟨n'⟩ := comp rfl m' mu
  obtain ⟨n₁⟩ := comp rfl n mu
  have hσ' : σ.symm H.w0 = H.w0 := σ.symm_apply_eq.2 hσ.symm
  let n₂ : SABMap (FiniteStable.twist σ.symm hσ' u) Z.t (spMap f ≫ χ) :=
    ⟨n₁.cm, n₁.cart, n₁.base, fun a => by
      have := n₁.act (σ.symm a)
      change _ = _ ≫ (Z.t.act.act (σ (σ.symm a))).left at this
      rwa [σ.apply_symm_apply] at this, n₁.lin⟩
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp f) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g : FractionRing W →+* FractionRing T'.V := IsFractionRing.lift j
  have e : jK T'.V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hr' : Set.range (jK T'.V ≫ spMap f ≫ χ') ⊆ Set.range Z'.j := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, ← hy', ← Category.assoc, ← e, Category.assoc]
  have hr : Set.range (jK T'.V ≫ spMap f ≫ χ) ⊆ Set.range Z.j := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y ≫ r) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, ← hy, ← Category.assoc, ← e, Category.assoc]
  have hW' : CDvr T'.V := ⟨T'.dvr, T'.cpl, T'.ch0⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  obtain ⟨be, hbe, hmon, -⟩ := exists_periodForm P hϖ
  obtain ⟨k', hk', hid'⟩ := hd' T'.V hW' ϖ hϖ _ u n' P hr' be hbe hmon
  obtain ⟨k, hk, hid⟩ := hd T'.V hW' ϖ hϖ _ _ n₂ (twistUnif σ.symm hσ' P) hr be
    ⟨hbe.1, fun a x z => by
      have := hbe.2.1 (σ.symm a) x z
      rw [← aut_bar] at this
      exact this, hbe.2.2⟩ hmon
  have hkk : (k : ℝ) = k' := hk.trans ((evalZ_twist hφ σ.symm hσ' _ be).trans hk'.symm)
  obtain rfl : k = k' := by exact_mod_cast hkk
  refine map_injective f hi ?_
  rw [← idlAlong_comp, ← idlAlong_comp]
  exact hid'.trans hid.symm

end GlobalTheory.TraitOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartValues
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.LineNorm

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem exists_fromSpec {A : Type} [CommRing A] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : Sp A ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* A, spMap φ ≫ hU.fromSpec = x := by
  have hr : Set.range x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact h (Set.mem_univ y)
  obtain ⟨φ, hφ⟩ := exists_spMap' (A := Γ(X, U)) (IsOpenImmersion.lift hU.fromSpec x hr)
  exact ⟨φ, hφ ▸ IsOpenImmersion.lift_fac _ _ hr⟩

theorem max_of_chart {R : Type} [CommRing R] {N : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (f : Sp ↥(intO C) ⟶ PSpace R N) (q : Fin (N + 1)) (hq : ⊤ ≤ f ⁻¹ᵁ chart R N q) (c : R →+* C)
    (w : Fin (N + 1) → C) (hw : Ideal.span (Set.range w) = ⊤) (h : spMap (intO C).subtype ≫ f = pt c w hw) :
    (∀ q', ‖w q'‖ ≤ ‖w q‖) ∧ w q ≠ 0 := by
  have := GlobalTheory.LatDRFree.intO_isLocalRing C
  obtain ⟨b, hb⟩ := exists_spMap' (f ≫ PSpace.str R N)
  obtain ⟨v, hv, rfl⟩ := exists_eq_pt b f hb
  rw [pt_preimage_chart] at hq
  have hu : IsUnit (v q) := by
    have h1 : IsLocalRing.closedPoint ↥(intO C) ∈ spOpen (v q) := hq (Set.mem_univ _)
    by_contra hn
    exact mem_spOpen.1 h1 hn
  rw [GlobalTheory.ProjSpace.spMap_pt] at h
  have hc : (intO C).subtype.comp b = c := by
    have h1 := congrArg (· ≫ PSpace.str R N) h
    simp only [pt_str] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hc
  obtain ⟨s, rfl⟩ := (pt_eq_pt_iff _ _ _).1 h
  have h1 : ‖(v q : C)‖ = 1 := by
    obtain ⟨a, ha⟩ := hu.exists_right_inv
    have h2 : ‖(v q : C)‖ * ‖(a : C)‖ = 1 := by
      rw [← norm_mul, ← norm_one (α := C)]
      exact congrArg (fun x : ↥(intO C) => ‖(x : C)‖) ha
    have h3 : ‖(v q : C)‖ ≤ 1 := (v q).2
    have h4 : ‖(a : C)‖ ≤ 1 := a.2
    nlinarith [norm_nonneg (v q : C), norm_nonneg (a : C)]
  have e : ∀ q', (s • ((intO C).subtype ∘ v)) q' = s.val * (v q' : C) := fun _ => rfl
  refine ⟨fun q' => ?_, ?_⟩
  · rw [e, e, norm_mul, norm_mul, h1]
    exact mul_le_mul_of_nonneg_left (v q').2 (norm_nonneg _)
  · rw [e]
    exact mul_ne_zero s.ne_zero (fun h0 => by simp [h0] at h1)

theorem log_norm_add_log_grNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → Down u → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (z : Sp ↥(intO C) ⟶ Z.X) a i (φ : Γ(Z.X, (Z.U a).1) →+* C), spMap φ ≫ Z.chart a = spMap (intO C).subtype ≫ z → ⊤ ≤ z ⁻¹ᵁ L'.U i → Real.log ‖valF (spMap (intO C).subtype ≫ z) _ (r a i).val‖ + Real.log (grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk) = 0 := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T n u kk h₀ h₁ L' ix q₀ q₁ r hL hu C _ _ z a i φ hφ hz
  have : (Y Z.i).X.IsSeparated := by
    have hp : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
    constructor
    rw [← terminal.comp_from (Y Z.i).s]
    infer_instance
  have hle := hz.trans (z.preimage_mono (hL.le i))
  have hU : ⊤ ≤ (z ≫ Z.π) ⁻¹ᵁ L.U (ix i) := fun y hy => (hle hy).1
  have hq₀ : ⊤ ≤ (z ≫ g ⟨kk, _, h₀⟩) ⁻¹ᵁ chart _ _ (q₀ i) := fun y hy => (hle hy).2.1
  have hq₁ : ⊤ ≤ (z ≫ g ⟨kk + 1, _, h₁⟩) ⁻¹ᵁ chart _ _ (q₁ i) := fun y hy => (hle hy).2.2
  obtain ⟨φO, hO⟩ := exists_fromSpec (aff (ix i)) _ hU
  have hx : spMap ((intO C).subtype.comp φO) ≫ (aff (ix i)).fromSpec = (spMap (intO C).subtype ≫ z) ≫ Z.π := by
    rw [Category.assoc, ← hO, ← Category.assoc]
    congr 1
    exact Spec.map_comp (CommRingCat.ofHom φO) (CommRingCat.ofHom (intO C).subtype)
  have hx' : spMap φ ≫ Z.chart a ≫ Z.π = (spMap (intO C).subtype ≫ z) ≫ Z.π := by rw [← hφ, Category.assoc]
  have P := GlobalTheory.FlagEmb.PlkPt.plk_pt E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T C a (ix i) φ _ (hx.trans hx'.symm)
  have hg : ∀ en, spMap (intO C).subtype ≫ z ≫ g en = spMap φ ≫ Z.chart a ≫ g en := fun en => by
    rw [← Category.assoc, ← hφ, Category.assoc]
  obtain ⟨hu₀, e₀⟩ := P ⟨kk, _, h₀⟩
  obtain ⟨hu₁, e₁⟩ := P ⟨kk + 1, _, h₁⟩
  obtain ⟨hun, -⟩ := P ⟨n, u, hu⟩
  obtain ⟨m₀, n₀⟩ := max_of_chart _ _ hq₀ _ _ _ ((hg _).trans e₀)
  obtain ⟨m₁, n₁⟩ := max_of_chart _ _ hq₁ _ _ _ ((hg _).trans e₁)
  have hv := hL.val C a i φ _ (hx.trans hx'.symm) (by
    rw [hφ]
    exact (spMap (intO C).subtype).preimage_mono hz)
  have key := GlobalTheory.FlagEmb.GradedNorm.sInf_mul_norm_plk C M n
    (fun j => crd (ix i) C ((intO C).subtype.comp φO) ((Z.fr a).bc φ (u j).1 (u j).2)) kk (q₀ i) (q₁ i)
    (span_range_eq_top_iff_ne_zero.1 hun) m₀ m₁
  have tan : ∀ j, IsTanAtG (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) ((Z.fr a).bc φ (u j).1 (u j).2) :=
    fun j => hx' ▸ ((T.frame a C φ).1 (u j).1 (u j).2).1
  have lat := fun w => GlobalTheory.LatDRCrd.mem_latDR_iff_crd E H _ (Y Z.i).t L aff M crd T.emb (ix i) C φO _ w hx
  have hS : grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)
      (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk =
      sInf {s : ℝ | ∃ cf : Fin n → C, cf kk ≠ 0 ∧ (∀ k, kk < k → cf k = 0) ∧ (∀ s, ‖(∑ j, cf j •
        crd (ix i) C ((intO C).subtype.comp φO) ((Z.fr a).bc φ (u j).1 (u j).2)) s‖ ≤ 1) ∧ s = ‖cf kk‖⁻¹} := by
    refine congrArg sInf (Set.ext fun s => exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_left fun _ => ⟨?_, fun hb => ?_⟩)
    · rintro ⟨w, hw, hc⟩
      have ht := comb_tan _ tan hc
      rw [← (T.emb.comb_iff _ _ hx tan ht cf).1 hc]
      exact (lat w ht).1 hw
    · obtain ⟨w, ht, hc⟩ := exists_comb _ tan cf
      refine ⟨w, (lat w ht).2 ?_, hc⟩
      rw [(T.emb.comb_iff _ _ hx tan ht cf).1 hc]
      exact hb
  rw [hS, ← hφ]
  have aux : ∀ (x A B : C) (s : ℝ), x * B = A → s * ‖A‖ = ‖B‖ → B ≠ 0 → Real.log ‖x‖ + Real.log s = 0 := by
    intro x A B s h1 h2 h3
    have h4 : ‖x‖ * s = 1 := by
      refine mul_right_cancel₀ (norm_ne_zero_iff.2 h3) ?_
      rw [← h1, norm_mul] at h2
      rw [one_mul]
      linear_combination h2
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h4) (right_ne_zero_of_mul_eq_one h4), h4, Real.log_one]
  exact aux _ _ _ _ hv key n₁

end GlobalTheory.FlagEmb.LineNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtFam

open GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem relAmple_iff_of_cls {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) : Out.RelAmple A M ↔ Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hL, relAmple_iff_isAmpleLB A hM]
  refine forall_congr' fun U => forall_congr' fun hU => ?_
  refine Iff.trans (isAmpleLB_congr (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)
    ((cls_eq_iff (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)).1 ?_)) (isAmpleLB_pow_iff (pull_isLB hL _) hd)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

section OneModel

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

theorem exists_keyAt (M : GChart Y) {R : Type} [CommRing R] {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hd : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, θ, ⟨hw, hr⟩, hθ, hne⟩ :=
    exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  have cast : ∀ (p q : Sp R ⟶ Y.X) (_ : p = q) (n : SABMap t Y.t p), ∃ n' : SABMap t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ _ (FlagMod.spMap_ev z M.hU hz).symm m
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp R) :=
    { A := t.G, g := M.n, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := hA, ktriv := hK
      isAb := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ _) m.base)
  have hrig : ∀ (e : Sp R ⟶ Y.X) (_ : m.cm.e = e) (he : eSec t.G ≫ m.φ = e ≫ eSec Y.t.G),
      rigPullOf m.φ e he Y.t.PP.L Y.t.PP.rig = m.cm.rigPull Y.t.PP.L Y.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨⟨P, hn, t.PP.rig, t.PP.rigGen, θ, fun s => ?_, v, hb⟩, rfl, m.φ, he, w, rfl, m.cart, hw, ?_,
    fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hne s
    exact ⟨g, hg, Opens.mem_iSup.2 ⟨i, hi⟩⟩
  · rw [hrig z m.base he]
    exact hr
  · exact (hθ (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))
  · rw [← hm']
    exact hv i

theorem exists_keyAt_of_point (M : GChart Y) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U) {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) {K : Type} [Field K] [CharZero K] (f : R →+* K) {x₀ : KeyIn K}
    (h₀ : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x₀) :
    ∃ x : KeyIn R, x.P.g = x₀.P.g ∧ KeyAt M z hz x := by
  obtain ⟨φ, -, w, hg, hc, hw, -⟩ := h₀
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : x₀.P.A.left ⟶ t.G.left, ψ ≫ m.φ = φ ∧ ψ ≫ t.G.hom = x₀.P.A.hom ≫ spMap f :=
    ⟨m.cart.1.lift φ (x₀.P.A.hom ≫ spMap f) (by rw [hc.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _,
      m.cart.1.lift_snd _ _ _⟩
  subst h₁
  have g : IsGrpPullback x₀.P.A t.G (spMap f) ψ := m.cart.cancel hc h₂
  have e : LBIso x₀.P.L (t.PP.L.pull ψ) :=
    LBIso.trans x₀.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB t.PP.isLB _) ⟨w, hw⟩
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ rfl).symm
  have hG : IsAbelianScheme t.G := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
  have q : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hK⟩ := KTrivGlob.exists_open t.PP.isLB x₀.P.isLB hG hA g e x₀.P.ktriv q
  have : CharZero R := f.charZero
  have : CharZero Γ(Sp R, ⊤) := charZero_of_injective_ringHom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  have kt := KTrivSpread.kTriv_of_open_integral GlobalTheory.firstFiveLaws.1 (Sp R) (fun n hn => Nat.cast_ne_zero.2 hn) U
    ⟨_, hU⟩ t.G t.PP t.cub hG hA hK
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (spMap f q))
  obtain rfl : d = M.n := (H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g.1 hd)
    x₀.P.smoothDim (eSec x₀.P.A q)).trans hg
  obtain ⟨x, hx, h⟩ := exists_keyAt M hz m hp hA kt hd (hg ▸ x₀.g_pos)
  exact ⟨x, hx.trans hg.symm, h⟩

end OneModel

end GlobalTheory.KeyAtFam
end
end

