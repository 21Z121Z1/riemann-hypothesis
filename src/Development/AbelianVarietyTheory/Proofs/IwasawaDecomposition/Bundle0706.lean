import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0689

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberRank
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext pushE left_pushE)

namespace GlobalTheory.LocM.LatCover

theorem exists_coordEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k _ x h hx τ mu hπ
  have hgen : ⊤ ≤ (x ≫ g) ⁻¹ᵁ B.genO := by
    intro z _
    have hz : x z ∈ Z.genO := CommonMod.mem_genO_of_mem_opn hp.ne_zero Z (hx ⟨z, rfl⟩)
    rw [← CommonMod.preimage_genO g] at hz
    exact hz
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ (V ⊓ B.genO) := fun z hz => ⟨h hz, hgen hz⟩
  let m' : Fin n → Γ(GlobalTheory.LieVB.omega B.t.G, V ⊓ B.genO) :=
    fun l => GlobalTheory.Twist.resM _ inf_le_left (L.N.incl.app V (m l))
  have hm' : GlobalTheory.VB.IsFrame m' := by
    refine (hm.res (inf_le_left : V ⊓ B.genO ≤ V)).map_of_linearEquiv
      (fun U hU => LinearEquiv.ofBijective (GlobalTheory.QCoh.appLinear L.N.incl U)
        ⟨L.N.incl_app_injective U, fun s => L.N.mem_sec_iff.1 (by
          rw [L.gen U (hU.trans inf_le_right)]
          trivial)⟩) fun U hU i => ?_

    show L.N.incl.app U (GlobalTheory.Twist.resM _ hU (GlobalTheory.Twist.resM _ inf_le_left (m i))) =
      GlobalTheory.Twist.resM _ hU (GlobalTheory.Twist.resM _ inf_le_left (L.N.incl.app V (m i)))
    rw [GlobalTheory.Twist.app_resM, GlobalTheory.Twist.app_resM]
  have tcomb : ∀ (r : ℕ) (u : Fin r → TanM (x ≫ g) B.t.G) (a : Fin r → k) (l : Fin n),
      tanEv B.t (isTan_tv (∑ i, a i • u i)) h' (m' l) = ∑ i, a i * tanEv B.t (isTan_tv (u i)) h' (m' l) :=
    fun r u a l => GlobalTheory.LocM.tanEv_comb E H B.X B.t k (x ≫ g) _ h' r (fun i => (tv (u i)).left)
      (fun i => isTan_tv (u i)) a _ (isTan_tv _) ((GlobalTheory.LieMet.isComb_iff u a _).2 rfl) (m' l)
  let ev : TanM (x ≫ g) B.t.G →ₗ[k] (Fin n → k) :=
    { toFun := fun v l => tanEv B.t (isTan_tv v) h' (m' l)
      map_add' := fun v w => funext fun l => by
        have e := tcomb 2 ![v, w] ![1, 1] l
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, _root_.one_mul] at e
        exact e
      map_smul' := fun c v => funext fun l => by
        have e := tcomb 1 ![v] ![c] l
        simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at e
        exact e }
  have hev : Function.Bijective ev := by
    constructor
    · intro v w hvw
      have u := (GlobalTheory.TanFibre.existsUnique_tanEv E H B.X B.t k (x ≫ g) _ h' n m' hm' (ev v)).unique
        ⟨isTan_tv v, fun l => rfl⟩ ⟨isTan_tv w, fun l => (congrFun hvw l).symm⟩
      exact tan_ext u
    · intro c
      obtain ⟨u, ⟨hu, hval⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H B.X B.t k (x ≫ g) _ h' n m' hm' c
      exact ⟨tanOf hu, funext hval⟩
  have hB : (x ≫ g) ≫ B.π = (x ≫ Z.π) ≫ τ := by
    rw [Category.assoc, Category.assoc, hπ]
  refine ⟨(pushE mu (x ≫ Z.π) rfl).trans ((pushE B.tMap (x ≫ g) hB).symm.trans (LinearEquiv.ofBijective ev hev)),
    fun w => ⟨_, isTan_tv ((pushE B.tMap (x ≫ g) hB).symm (pushE mu (x ≫ Z.π) rfl w)), ?_, fun l => ?_⟩⟩
  · rw [← left_pushE B.tMap (x ≫ g) hB, LinearEquiv.apply_symm_apply]
    rfl
  · exact (GlobalTheory.LocM.tanEv_resM B.t _ h' inf_le_left _).symm

end GlobalTheory.LocM.LatCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepFrameFiber
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocM.LatNorm

theorem fromSpec_appLE_top' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem val_appLE {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {k : Type} [CommRing k]
    (φ : Γ(X, U) →+* k) (g : X ⟶ Y) {O : Y.Opens} (hle : U ≤ g ⁻¹ᵁ O)
    (h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ O) (s : Γ(Y, O)) :
    (Scheme.ΓSpecIso (.of k)).hom (((spMap φ ≫ hU.fromSpec) ≫ g).appLE O ⊤ h s) = φ (g.appLE O U hle s) := by
  have e₀ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e₁ : ⊤ ≤ spMap φ ⁻¹ᵁ (⊤ : (Sp Γ(X, U)).Opens) := le_top
  have e : ((spMap φ ≫ hU.fromSpec) ≫ g).appLE O ⊤ h =
      g.appLE O U hle ≫ hU.fromSpec.appLE U ⊤ e₀ ≫ (spMap φ).appLE ⊤ ⊤ e₁ := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  have h1 : (spMap φ).appLE ⊤ ⊤ e₁ = (spMap φ).appTop := Scheme.Hom.appLE_eq_app _
  rw [e, fromSpec_appLE_top', h1]
  have := congrArg (fun f => f.hom ((Scheme.ΓSpecIso Γ(X, U)).inv (g.appLE O U hle s)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.comp_apply] at this ⊢
  refine this.trans ?_
  exact congrArg φ (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, U)) _)

open GlobalTheory.Twist (resM app_resM)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem tanEv_incl_res {B : Mdl Y i₀} (L : Lat B) {k : Type} [CommRing k] {x : Sp k ⟶ B.X}
    {v : Sp (DualNumber k) ⟶ B.t.G.left} (hv : IsTanAtG B.t x v) {V O : B.X.Opens} (hOV : O ≤ V)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (hO : ⊤ ≤ x ⁻¹ᵁ O) (s : Γ(L.N.toMod, V)) :
    tanEv B.t hv h (L.N.incl.app V s) = tanEv B.t hv hO (L.N.incl.app O (resM _ hOV s)) := by
  rw [app_resM, tanEv_resM]

theorem tanEv_incl_sum {B : Mdl Y i₀} (L : Lat B) {k : Type} [CommRing k] {x : Sp k ⟶ B.X}
    {v : Sp (DualNumber k) ⟶ B.t.G.left} (hv : IsTanAtG B.t x v) {O : B.X.Opens} (hO : ⊤ ≤ x ⁻¹ᵁ O) {n : ℕ}
    (c : Fin n → Γ(B.X, O)) (s : Fin n → Γ(L.N.toMod, O)) :
    tanEv B.t hv hO (L.N.incl.app O (∑ i, c i • s i)) =
      ∑ i, (Scheme.ΓSpecIso (.of k)).hom (x.appLE O ⊤ hO (c i)) * tanEv B.t hv hO (L.N.incl.app O (s i)) := by
  let f : Γ(B.om, O) →+ k := AddMonoidHom.mk' (tanEv B.t hv hO) (tanEv_add B.t hv hO)
  have e : tanEv B.t hv hO (L.N.incl.app O (∑ i, c i • s i)) = f (L.N.incl.app O (∑ i, c i • s i)) := rfl
  rw [e, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul]
  exact tanEv_smul B.t hv hO _ _

theorem stepAt_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ) (g : Z.X ⟶ B.X), IsMap Z B g → Step.Holds ⟨B, L, σ, r, hr⟩ Z → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ x : Z.X, g x ∈ V → ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (a : GL (Fin n) Γ(Z.X, U)), x ∈ U ∧ U ≤ g ⁻¹ᵁ V ∧ LatCover.StepAt Z B g L σ r hU m a := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L σ r hr g hg hH V n m hm x hx
  obtain ⟨-, g', hg', hS⟩ := hH
  dsimp only at g' hg' hS
  obtain rfl := GlobalTheory.LocM.MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW Z B g' g hg' hg
  obtain ⟨U', hU', V', n', m', a', hxU', hU'V', hm', hcl⟩ := hS x
  have hxO : g' x ∈ V ⊓ V' := ⟨hx, hU'V' hxU'⟩
  haveI : Nontrivial Γ(B.X, V ⊓ V') := (B.X.presheaf.germ (V ⊓ V') (g' x) hxO).hom.domain_nontrivial
  let b := hm.basis (inf_le_left : V ⊓ V' ≤ V)
  let b' := hm'.basis (inf_le_right : V ⊓ V' ≤ V')
  obtain rfl : n = n' := by simpa using Fintype.card_congr (b.indexEquiv b')
  obtain ⟨U, hU, hxU, hUle⟩ := GlobalTheory.QCoh.exists_affine_mem_le (U := U' ⊓ g' ⁻¹ᵁ (V ⊓ V')) x ⟨hxU', hxO⟩
  have hUU' : U ≤ U' := hUle.trans inf_le_left
  have hUO : U ≤ g' ⁻¹ᵁ (V ⊓ V') := hUle.trans inf_le_right
  have hUV : U ≤ g' ⁻¹ᵁ V := hUO.trans (g'.preimage_mono inf_le_left)
  let gU : Γ(B.X, V ⊓ V') →+* Γ(Z.X, U) := (g'.appLE (V ⊓ V') U hUO).hom
  let T := b.toMatrix b'
  let S := b'.toMatrix b
  let Mu : GL (Fin n) Γ(Z.X, U) := ⟨(T.map gU).transpose, (S.map gU).transpose,
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ gU.map_zero gU.map_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ gU.map_zero gU.map_one, Matrix.transpose_one]⟩
  let a : GL (Fin n) Γ(Z.X, U) := Matrix.GeneralLinearGroup.map (GlobalTheory.LocM.StepFrame.resR hUU') a' * Mu
  refine ⟨U, hU, a, hxU, hUV, ?_⟩
  intro k _ φ v hv h hin j hj
  have ept : spMap (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) ≫ hU'.fromSpec = spMap φ ≫ hU.fromSpec := by
    have sc : spMap (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) = spMap φ ≫ spMap (GlobalTheory.LocM.StepFrame.resR hUU') := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [sc, Category.assoc, GlobalTheory.LocM.StepFrame.spMap_resR hU' hU hUU']
  have key := hcl k (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) v
  rw [ept] at key
  have hfU : ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_rfl
  have hO : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g') ⁻¹ᵁ (V ⊓ V') := by
    rw [Scheme.Hom.comp_preimage]
    exact hfU.trans ((spMap φ ≫ hU.fromSpec).preimage_mono hUO)
  have hV' : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g') ⁻¹ᵁ V' := hO.trans (Scheme.Hom.preimage_mono _ inf_le_right)
  have k0 := key hv hV' hin j hj

  have hb : ∀ l, b l = resM _ (inf_le_left : V ⊓ V' ≤ V) (m l) := fun l => hm.basis_apply _ _
  have hb' : ∀ l, b' l = resM _ (inf_le_right : V ⊓ V' ≤ V') (m' l) := fun l => hm'.basis_apply _ _
  have e₁ : ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = tanEv B.t hv hO (L.N.incl.app (V ⊓ V') (b l)) := fun l => by
    rw [hb]
    exact tanEv_incl_res L hv inf_le_left h hO (m l)
  have e₂ : ∀ l', tanEv B.t hv hV' (L.N.incl.app V' (m' l')) =
      ∑ i, φ (gU (T i l')) * tanEv B.t hv hO (L.N.incl.app (V ⊓ V') (b i)) := fun l' => by
    rw [tanEv_incl_res L hv inf_le_right hV' hO (m' l'), ← hb', ← b.sum_toMatrix_smul_self b' l', tanEv_incl_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [val_appLE hU φ g' hUO]
  have e₃ : ∀ l, φ (a j l) = ∑ l', φ (GlobalTheory.LocM.StepFrame.resR hUU' (a' j l')) * φ (gU (T l l')) := fun l => by
    have ea : (a : Matrix (Fin n) (Fin n) Γ(Z.X, U)) = (Matrix.GeneralLinearGroup.map (GlobalTheory.LocM.StepFrame.resR hUU') a' :
        Matrix (Fin n) (Fin n) Γ(Z.X, U)) * (Mu : Matrix (Fin n) (Fin n) Γ(Z.X, U)) := Units.val_mul _ _
    rw [ea, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [map_mul]
    rfl
  simp only [e₂, RingHom.comp_apply] at k0
  simp only [e₁, e₃, Finset.sum_mul, Finset.mul_sum, mul_assoc] at k0 ⊢
  rw [Finset.sum_comm]
  exact k0

end GlobalTheory.LocM.LatNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  first | exact @GlobalTheory.lbIso_of_generic_normal_local | exact GlobalTheory.lbIso_of_generic_normal_local | (intros; apply GlobalTheory.lbIso_of_generic_normal_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HeckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

def LvlPsi (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  (∀ g : G, g ∈ F.P0 ↔ (R.eG.trans cG) g ∈ Formalism.IndefR.NX.U D.nd) ∧
    ∀ (u : F.P0) (hu : (R.eG.trans cG) u ∈ Formalism.IndefR.NX.U D.nd),
      (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = (((F.ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

end Clauses

section Rat

variable {D : D7}

def FormsC (S : RatDat D.ntw) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ FiniteDimensional S.Ks (FmK S j) ∧
    ∃ T : Finset (S.WL j), (∀ x ∈ T, x ∈ (S.A j).MK) ∧
      (∀ x ∈ (S.A j).MK, x ∈ (S.A j).WK ∧ x ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j))) ∧
      ∀ x ∈ (S.A j).WK, x ∈ Submodule.span S.Ks (T : Set (S.WL j))

def StabC (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK

def IntC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j k P, 1 ≤ j → j ≤ D.R.m → IsSplitPl D.host P → P ∉ Sb → k ≤ D.R.r → ∃ n : ℕ,
    ∀ x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), x ∈ goodL D S θ j →
      (normV P) ^ n • hL j k P x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j))

def SpanC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → goodL D S θ j ≤
    ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb), Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL)

def lowSet (D : D7) : Set (PlE D.host) := {v | ∃ p ∈ lowAll D, p ≠ 0 ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}

theorem lowSet_finite (D : D7) : (lowSet D).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (s := (((lowAll D).filter (· ≠ 0) : Finset ℕ) : Set ℕ)) (Finset.finite_toSet _)
    fun p hp => GlobalTheory.RowTie.placesOver_finite_of_ne_zero D.host.E p (Finset.mem_filter.1 hp).2) ?_
  rintro v ⟨p, hp, hp0, hv⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hp, hp0⟩)) hv

def SbD (D : D7) : Finset (PlE D.host) := (lowSet_finite D).toFinset

theorem overSet_SbD (D : D7) : OverSet D (SbD D) (lowAll D) := by
  intro v hv
  obtain ⟨p, hp, -, hv⟩ := (lowSet_finite D).mem_toFinset.1 hv
  exact ⟨p, hp, hv⟩

end Rat

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def kKsOf (x : St P) : x.m.z.core.Q.c.F →+* ↥(Dof x).LL0 :=
  (algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL).codRestrict (Dof x).LL0 x.m.z.fieldValues_mem_fixedField

theorem hkOf (x : St P) (y : x.m.z.core.Q.c.F) :
    ((kKsOf x y : ↥(Dof x).LL0) : (Dof x).what₂.LL) = algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL y := rfl

abbrev SOf (x : St P) : RatDat (Dof x).ntw := ratDatR x.m.z.R x.m.z.cG (kKsOf x) (hkOf x)

end State

end GlobalTheory.HeightCounting.RatSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace Mark

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

def InFace (β x : LinearMap.BilinForm ℤ X) : Prop :=
  x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ (∀ y, β y y = 0 → x y y = 0) ∧
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x ∧ lab.evalZ (β + x) = lab.evalZ β

def IsIndec (β x : LinearMap.BilinForm ℤ X) : Prop :=
  InFace bar ψ lab β x ∧ x ≠ 0 ∧ ∀ y z, InFace bar ψ lab β y → InFace bar ψ lab β z → y ≠ 0 → z ≠ 0 → y + z ≠ x

variable (X) in

def IsMarked (β : LinearMap.BilinForm ℤ X) : Prop :=
  β ∈ balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    lab.evalZ β = ((i + 1 : ℕ) : ℝ) ∧
    ∃ S : Finset (LinearMap.BilinForm ℤ X), (∀ x, x ∈ S ↔ IsIndec bar ψ lab β x) ∧
      ∃ k : ℕ, 0 < k ∧ (k : ℤ) • β = ∑ x ∈ S, x

open Classical in

def markVal (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : ℝ :=
  if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b then
    (if IsMarked bar ψ lab i (Fin n → O) h.choose then 1 else 0) else 0

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

open Classical in

theorem markVal_int (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    markVal bar ψ lab i n (fun a b => (β a b : ℝ)) = if IsMarked bar ψ lab i (Fin n → O) β then 1 else 0 := by
  classical
  unfold markVal
  have h : ∃ β' : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, ((β a b : ℤ) : ℝ) = β' a b := ⟨β, fun _ _ => rfl⟩
  rw [dif_pos h]
  have e : h.choose = β := LinearMap.ext₂ fun a b => by
    have := h.choose_spec a b
    exact_mod_cast this.symm
  rw [e]

example : InFace (id : ℤ → ℤ) (zeroFun ℤ) (zeroFun ℤ) mulForm mulForm :=
  ⟨mem_balForms_int.2 fun y z => by simp [mul_comm], fun y => by simp [mul_self_nonneg], fun y h => h,
    by simp, by simp⟩

end Basic

end Mark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealMapOfGermsAffineScheme
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GermAff

theorem mem_map_of_germ : ∀ {T Y' : Scheme.{0}} [IsAffine T] (χ : T ⟶ Y') (I : Y'.IdealSheafData) (W : Y'.affineOpens)
    (hle : ⊤ ≤ χ ⁻¹ᵁ (W : Y'.Opens)) (s : Γ(T, ⊤)),
    (∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ FinalTheorems.stalkId (I.comap χ) t) →
      s ∈ (I.ideal W).map (χ.appLE W ⊤ hle).hom := by
  intro T Y' _ χ I W hle s hs
  set K := (I.ideal W).map (χ.appLE W ⊤ hle).hom with hK
  have hc : I.comap χ = Scheme.IdealSheafData.ofIdealTop K := by
    refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
    have hz : χ z ∈ W.1 := hle trivial
    rw [GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map I W _ hz, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
    congr 3
    exact T.presheaf.germ_res (homOfLE hle) z (by trivial)
  have hs' : ∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ K.map (T.presheaf.germ ⊤ t trivial).hom := by
    intro t
    rw [← GlobalTheory.LocM.stalkId_ofIdealTop, ← hc]
    exact hs t
  by_contra hns
  have hne : K.colon {s} ≠ ⊤ := by
    intro htop
    have h1 : (1 : Γ(T, ⊤)) ∈ K.colon {s} := htop ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hns h1
  obtain ⟨P, hP, hCP⟩ := Ideal.exists_le_maximal _ hne
  let y : PrimeSpectrum Γ(T, ⊤) := ⟨P, hP.isPrime⟩
  have hA := isAffineOpen_top T
  let t : T := hA.fromSpec y
  have ht : t ∈ (⊤ : T.Opens) := trivial
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk t) := T.presheaf.algebra_section_stalk ⟨t, ht⟩
  haveI : IsLocalization y.asIdeal.primeCompl (T.presheaf.stalk t) := hA.isLocalization_stalk' y ht
  have hg : (T.presheaf.germ ⊤ t trivial).hom = algebraMap Γ(T, ⊤) (T.presheaf.stalk t) := rfl
  have h := hs' t
  rw [hg, IsLocalization.mem_map_algebraMap_iff y.asIdeal.primeCompl] at h
  obtain ⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, he⟩ := h
  simp only at he
  rw [← map_mul, IsLocalization.eq_iff_exists y.asIdeal.primeCompl] at he
  obtain ⟨⟨c, hcm⟩, hc'⟩ := he
  simp only at hc'
  have hmem : c * m ∈ K.colon {s} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have : c * m * s = c * k := by rw [← hc']; ring
    rw [this]
    exact K.mul_mem_left c hk
  have hnot : c * m ∉ P := fun h' => (hP.isPrime.mem_or_mem h').elim hcm hm
  exact hnot (hCP hmem)

end GlobalTheory.GermAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealSheafMapOfAffineCoverPreimage
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.IdealPushCover

theorem mem_map_ideal_of_cover : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] (I : Y'.IdealSheafData) (U : X.affineOpens) {ι : Type} (W : ι → Y'.affineOpens) (hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) → ∀ b : Γ(X, U), (∀ i, (ρ.appLE U (W i) (hW i)).hom b ∈ I.ideal (W i)) → b ∈ (I.map ρ).ideal U := by
  intro X Y' ρ _ I U ι W hW hcov b hb
  have hk : ∀ V : Y'.affineOpens, I.ideal V = RingHom.ker (I.subschemeι.app V.1).hom := fun V => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]
  change (I.subschemeι.app (ρ ⁻¹ᵁ U.1)).hom ((ρ.app U.1).hom b) = 0
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  rw [map_zero]
  have hz' : I.subschemeι z ∈ ⨆ i, (W i : Y'.Opens) := hcov hz
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hzi : z ∈ I.subschemeι ⁻¹ᵁ (W i : Y'.Opens) := hi
  have h0 : (I.subschemeι.app (W i).1).hom ((ρ.appLE U (W i) (hW i)).hom b) = 0 := by
    have := hb i
    rw [hk, RingHom.mem_ker] at this
    exact this
  have e1 : (ρ.appLE U (W i) (hW i)).hom b = resG Y' (hW i) ((ρ.app U.1).hom b) := rfl
  rw [e1, GlobalTheory.Cartier.app_resG] at h0
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono (hW i)) z hzi, h0, map_zero]

end GlobalTheory.IdealPushCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGram
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem goodBound_congr_nhds (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ)
    (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  intro h hb
  have hv : G v = G' v := h.eq_of_nhds
  have hc : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn G u ξ) =ᶠ[nhds v] (fun u => GlobalTheory.HermFrame.conn G' u ξ) :=
    fun ξ => h.eventuallyEq_nhds.mono fun x hx => GlobalTheory.HermFrame.conn_congr hx ξ
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · rw [← hv]; exact hb.entry i j
  · rw [← hv]; exact hb.det
  · rw [← GlobalTheory.HermFrame.conn_congr h]; exact hb.form a i j
  · rw [← GlobalTheory.HermFrame.curv_congr h]; exact hb.dbar a b i j
  · rw [← GlobalTheory.HermFrame.mdel_congr (hc _), ← GlobalTheory.HermFrame.mdel_congr (hc _)]; exact hb.del a b i j

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBoundedStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polFanCarrierDimension_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  first | exact @GlobalTheory.PolFan.carrierDim_bounded | exact GlobalTheory.PolFan.carrierDim_bounded | (intros; apply GlobalTheory.PolFan.carrierDim_bounded <;> assumption)
end

