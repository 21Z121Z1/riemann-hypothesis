import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3352
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartPeriodTauZeroValueOne
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

noncomputable section

namespace GlobalTheory.UnitTauZero

theorem exists_isUnitTau_zero_val_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  have hF : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim
      (K' := Fin 4) ![(P.D.toPre.c (mu + 0)).left, (P.D.toPre.c mu).left, (P.D.toPre.c 0).left, (P.D.toPre.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [add_zero, Finset.univ_eq_empty, Finset.prod_empty, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    simp [Matrix.vecHead, Matrix.vecTail]
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen P.D.toPre.P.isLB hF (LB.oneGen P.D.toPre.P.L) (LB.isGen_oneGen _)
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨τ₀, ⟨hτ, 1, ?_, fun zz J hJ => ?_⟩, h1⟩
  · simp
  · have hB : P.D.toPre.TauBimult := P.D.tau_bimult
    rw [h1 _ _ zz J hJ, _root_.mul_one]
    have vτ : val (P.D.toPre.tau mu 0) (𝟙 _) zz J =
        val (P.D.toPre.psi (mu + 0)) (𝟙 _) zz J * (val (P.D.toPre.psi mu) (𝟙 _) zz J)⁻¹ *
          (val (P.D.toPre.psi 0) (𝟙 _) zz J)⁻¹ * (val P.D.toPre.rigK (𝟙 _) zz J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have vρ : val P.D.toPre.rigK (𝟙 _) zz J = val P.D.toPre.rig (jK _) zz J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ a : P.D.toPre.X, a = mu → val (P.D.toPre.psi a) (𝟙 _) zz J = val (P.D.toPre.psi mu) (𝟙 _) zz J := by
      rintro a rfl; rfl
    have h0 := GlobalTheory.PsiZero.val_psi_zero hB hJ
    have hu : unitOn (1 : (FractionRing (ChartRing k m d))ˣ) = 1 := map_one _
    rw [vτ, hp _ (add_zero mu), h0, vρ, hu, map_one, mul_inv_cancel, _root_.one_mul, inv_inv, mul_inv_cancel]

end GlobalTheory.UnitTauZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitValueTranslatedBundleSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitPt

theorem isUnit_gs_of_mem_basicOpen {X Y : Scheme.{0}} (T : X ⟶ Y) (x : X) (U : Y.Opens) (h : T x ∈ U) (a : Γ(Y, U))
    (ha : T x ∈ Y.basicOpen a) : IsUnit (gs T x U a) := by
  rw [gs_eq T x U h]
  have hu := (Y.mem_basicOpen a (T x) h).1 ha
  rw [← Scheme.Hom.germ_stalkMap_apply T U x h a]
  exact hu.map _

theorem exists_unit_sval (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (α ν : Q.X)
    (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k))) (hs : ¬ ∀ j, s.f j = 0) :
    ∃ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι),
      Good Q.P.L z J ∧ IsUnit (sval s (DegPre.trF Q (FractionRing R) ν).left z J) := by
  obtain ⟨j, hj⟩ := not_forall.1 hs
  have hsm := Q.P.isAb.smooth
  let p : (DegPre.BF Q (FractionRing R)).left ⟶ Spec (CommRingCat.of (FractionRing R)) :=
    (fst (TF (R := R) (FractionRing R)) Q.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) (FractionRing R)).hom Q.P.A.hom))
  have : IsReduced (DegPre.BF Q (FractionRing R)).left := isReduced_of_smooth p
  have hne : (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) ≠ ⊥ := fun h =>
    hj ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) := by
    by_contra h
    push_neg at h
    exact hne (eq_bot_iff.2 fun x hx => (h x hx).elim)
  have hwU := Scheme.basicOpen_le _ _ hw
  set T := (DegPre.trF Q (FractionRing R) ν).left with hT
  let z := (DegPre.trF Q (FractionRing R) (-ν)).left w
  have hz : T z = w := by
    change ((DegPre.trF Q (FractionRing R) (-ν)).left ≫ T) w = w
    rw [hT, ← Over.comp_left, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_add, neg_add_cancel, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_zero]
    rfl
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.P.L z J := ⟨_, fun ψ => (exists_chart Q.P.isLB (ψ z)).choose_spec⟩
  refine ⟨z, J, hJ, ?_⟩
  have hz' : T z ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) α) j := hz ▸ hwU
  have hzb : T z ∈ (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) := hz ▸ hw
  rw [sval, sec_trans s T z (hJ.mem _ T) hz']
  exact (Units.isUnit _).mul (isUnit_gs_of_mem_basicOpen T z _ hz' (s.f j) hzb)

end GlobalTheory.UnitPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivation
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

namespace GlobalTheory.DerFieldExt

theorem cover' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) :
    W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

theorem sep' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) (s t : Γ(X, W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k s = resG X k t) : s = t :=
  X.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
    W (fun i => homOfLE i.2) (cover' X hW h) s t (fun i => e i.1 i.2)

theorem exists_field : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U),
    (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) →
    ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  intro X W₀ hW d₀ hadd hmul
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(X, X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG X (X.basicOpen_le f) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    obtain ⟨δ, h1, h2, h3⟩ := GlobalTheory.LocDerExt.der_exists f (RingHom.id _)
      (fun a => resG X (X.basicOpen_le f) (d₀ a)) (fun a b => by simp only [hadd, map_add])
      (fun a b => by simp only [hmul, map_add, map_mul, RingHom.id_apply]; rfl)
    exact ⟨δ, h1, fun a b => by simpa using h2 a b, h3⟩
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG X k (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine GlobalTheory.LocDerExt.der_unique f (resG X k)
      (fun s => resG X k (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add, map_mul]
    · simp only [δmul, map_mul]
    · change resG X k (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [GlobalTheory.LocDerExt.res_res X, δres, δres, GlobalTheory.LocDerExt.res_res X]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(X, W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
      W (fun i => homOfLE i.2) (cover' X hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : X.basicOpen i.1 ⊓ X.basicOpen j.1 ≤ X.basicOpen (i.1 * j.1) := e.ge
        have e' : resG X ki (δ i.1 (resG X i.2 s)) = resG X kj (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X]
        have e'' := congrArg (resG X k) e'
        rw [GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add, δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add, map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep' X hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (GlobalTheory.LocDerExt.res_res X h' k _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), GlobalTheory.LocDerExt.res_res X]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep' X hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.DerFieldExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldGluedOpenCover
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

noncomputable section

namespace GlobalTheory.LogKS.Glue

variable {Z : Scheme.{0}}

theorem resG_resG {U V W : Z.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (f : Γ(Z, U)) :
    resG Z h2 (resG Z h1 f) = resG Z (h2.trans h1) f := by
  change (Z.presheaf.map (homOfLE h1).op ≫ Z.presheaf.map (homOfLE h2).op).hom f = _
  rw [← Functor.map_comp]
  rfl

variable {J : Type} (V : J → Z.Opens) (e : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O))

def loc (O : Z.Opens) (f : Γ(Z, O)) (i : J) : Γ(Z, O ⊓ V i) :=
  e i (O ⊓ V i) (resG Z inf_le_left f)

open Classical in

def glue (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : ∃ s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i then h.choose else 0

variable {V e}

theorem compat (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) (O : Z.Opens) (f : Γ(Z, O)) :
    TopCat.Presheaf.IsCompatible Z.sheaf.1 (fun i => O ⊓ V i) (loc V e O f) := by
  intro i j
  change resG Z (inf_le_left : (O ⊓ V i) ⊓ (O ⊓ V j) ≤ O ⊓ V i) (loc V e O f i) =
    resG Z (inf_le_right : (O ⊓ V i) ⊓ (O ⊓ V j) ≤ O ⊓ V j) (loc V e O f j)
  simp only [loc]
  rw [← (he i).2.2 (O ⊓ V i) _ inf_le_left inf_le_right, ← (he j).2.2 (O ⊓ V j) _ inf_le_right inf_le_right,
    resG_resG, resG_resG]
  exact hc i j _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) _

theorem glue_ex (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) :
    ∃! s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i :=
  Z.sheaf.existsUnique_gluing' (fun i => O ⊓ V i) O (fun i => homOfLE inf_le_left)
    ((le_inf le_rfl hO).trans (inf_iSup_eq _ _).le) (loc V e O f) (compat he hc O f)

theorem glue_eq (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) (s : Γ(Z, O))
    (hs : ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i) : glue V e O f = s := by
  obtain ⟨t, -, hu⟩ := glue_ex he hc hO f
  have h : ∃ s : Γ(Z, O), ∀ i, resG Z (inf_le_left : O ⊓ V i ≤ O) s = loc V e O f i := ⟨s, hs⟩
  rw [glue, dif_pos h]
  exact (hu _ h.choose_spec).trans (hu _ hs).symm

theorem res_glue (he : ∀ i, IsField (V i) (e i))
    (hc : ∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) {O : Z.Opens}
    (hO : O ≤ ⨆ i, V i) (f : Γ(Z, O)) (i : J) :
    resG Z (inf_le_left : O ⊓ V i ≤ O) (glue V e O f) = loc V e O f i := by
  obtain ⟨t, ht, -⟩ := glue_ex he hc hO f
  rw [glue_eq he hc hO f t ht]
  exact ht i

end GlobalTheory.LogKS.Glue

theorem GlobalTheory.LogKS.isField_glue : ∀ (Z : Scheme.{0}) (J : Type) (V : J → Z.Opens) (e : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), (∀ i, IsField (V i) (e i)) → (∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (⨆ i, V i) d ∧ ∀ i (O : Z.Opens), O ≤ V i → ∀ f, d O f = e i O f := by
  intro Z J V e he hc
  open GlobalTheory.LogKS.Glue in
  refine ⟨glue V e, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W hW f f'
    refine glue_eq he hc hW _ _ fun i => ?_
    rw [map_add, res_glue he hc hW f, res_glue he hc hW f']
    simp only [loc, map_add]
    exact ((he i).1 _ inf_le_right _ _).symm
  · intro W hW f f'
    refine glue_eq he hc hW _ _ fun i => ?_
    rw [map_add, map_mul, map_mul, res_glue he hc hW f, res_glue he hc hW f']
    simp only [loc, map_mul]
    exact ((he i).2.1 _ inf_le_right _ _).symm
  · intro W W' h hW f
    refine glue_eq he hc (h.trans hW) _ _ fun i => ?_
    rw [resG_resG, ← resG_resG (inf_le_left : W ⊓ V i ≤ W) (inf_le_inf_right (V i) h), res_glue he hc hW f]
    simp only [loc]
    rw [← (he i).2.2 _ _ (inf_le_inf_right (V i) h) inf_le_right, resG_resG, resG_resG]
  · intro i O hO f
    refine glue_eq he hc (hO.trans (le_iSup V i)) _ _ fun j => ?_
    simp only [loc]
    rw [← (he i).2.2 O (O ⊓ V j) inf_le_left hO f]
    exact hc i j _ (inf_le_left.trans hO) inf_le_right _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportStatementOfDiscreteSeries
section
set_option autoImplicit false

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem exportSt_of_hypotheses (hC : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity)
    (hR : GlobalTheory.Published.RayClassFieldSt) (hD : GlobalTheory.Published.DiscreteSeriesCover) (hW : GlobalTheory.Published.CasselmanWallach)
    (hS : GlobalTheory.SerStd.SeriesRatS) : ExportSt :=
  have tA := GlobalTheory.T.twAdm'
  have tC := GlobalTheory.T.twist_character_of_artin hA tA
  have row := GlobalTheory.T.row_statement_of_low_weight hC hA hR hS GlobalTheory.T.low_weight_statement tA
  Steps.exportSt ⟨GlobalTheory.T.canonical_existence, GlobalTheory.T.canonical_projection, tA, row, GlobalTheory.T.rationality_of_twist_row tA row, GlobalTheory.T.reciprocity_side_of_twist tA, GlobalTheory.T.adapted_existence,
    GlobalTheory.T.conjugate_base_of_reciprocity hC hA hR hS, GlobalTheory.T.conjugate_twist_of_discrete_series hC hA hR hD hW hS tA tC, GlobalTheory.T.base_upper_bound hC hA hR, GlobalTheory.T.base_lower_bound hC hA hR hS,
    GlobalTheory.T.twist_upper_bound hC hA hR tA tC, GlobalTheory.T.twGe_of_print_twAdm_twChr hC hA hR hS tA tC⟩

end GlobalTheory.BigOn.Exp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTop
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

namespace GlobalTheory.BaseChangeAffine

theorem closure_range_union_eq_top_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (h : IsPushout f g i j) :
    Subring.closure (Set.range i.hom ∪ Set.range j.hom) = ⊤ := by
  set R := Subring.closure (Set.range i.hom ∪ Set.range j.hom)
  let l : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (i.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let r : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (j.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ l = g ≫ r := by
    ext a
    have := congrArg (fun q : A ⟶ P => q.hom a) h.w
    simpa [l, r] using this
  let s : CommRingCat.of R ⟶ P := CommRingCat.ofHom R.subtype
  have hid : h.desc l r w ≫ s = 𝟙 P := by
    apply h.hom_ext
    · ext b; simp [l, s]
    · ext c; simp [r, s]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (((h.desc l r w).hom x : R) : P) = x := by
    have := congrArg (fun q : P ⟶ P => q.hom x) hid
    simpa [s] using this
  rw [← hx]
  exact ((h.desc l r w).hom x).2

theorem affine_and_closure_eq_top : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (O : Z.affineOpens), O.1 ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) ∧ Subring.closure (Set.range (φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left).hom ∪ Set.range (p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right).hom) = ⊤ := by
  intro Z Z' X X' p p' φ g H U U' hU' O hO
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine U'.1.toScheme := U'.2
  have : IsAffine O.1.toScheme := O.2
  have hpb := Scheme.Hom.isPullback_resLE H (US := U.1) (UT := U'.1) (UX := O.1)
    (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) hU' hO rfl
  refine ⟨.of_isIso hpb.isoPullback.hom, ?_⟩
  have po := (isIso_pushoutSection_iff H hU' hO (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) rfl).1
    (isIso_pushoutSection_of_isAffineOpen H hU' hO rfl U.2 U'.2 O.2)
  exact closure_range_union_eq_top_of_isPushout po

end GlobalTheory.BaseChangeAffine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackAbelianSchemeDualNumberEq
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

namespace GlobalTheory.DualRigidityField

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem eq_of_eq_closedFibre {K : Type} [Field K] (A' G' : Over (Sp (DualNumber K))) [GrpObj A'] [GrpObj G']
    (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hab : pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ a.left =
      pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ b.left)
    (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  haveI := subsingleton_sp_dualNumber K
  let j := pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
  have hj : IsPullback j (pullback.snd A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) A'.hom
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := IsPullback.of_hasPullback _ _
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (GlobalTheory.globalFns_holds _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

theorem pullback_eq : ∀ {R : Type} [CommRing R] (k : Type) [Field k] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (f : R →+* DualNumber k) (π₁ π₂ : B'.left ⟶ A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsGrpPullback B' A (spMap f) π₁ → IsGrpPullback B' A (spMap f) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ = π₂ := by
  intro R _ k _ A _ g B' _ f π₁ π₂ hA hg h1 h2 hx
  have hB := (GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A B' π₂ g h2 hA hg).1
  let α : B' ⟶ B' := Over.homMk (h2.1.lift π₁ B'.hom h1.1.w) (h2.1.lift_snd _ _ _)
  have hα : α.left ≫ π₂ = π₁ := h2.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom h1 h2 (𝟙 A) α (by rw [hα]; rfl)
  have hα1 : α = 𝟙 B' := by
    refine eq_of_eq_closedFibre B' B' α (𝟙 B') hB ?_ (by rw [IsMonHom.one_hom, Category.comp_id])
    apply h2.1.hom_ext
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [hα]
      exact hx _ _ _ pullback.condition
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [Over.w α]
  rw [← hα, hα1, Over.id_left, Category.id_comp]

end GlobalTheory.DualRigidityField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinearStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_natural_semilinear : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] G'.RigExt), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k' (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  first | (exact @GlobalTheory.Katz.rig_pull_natural_semi) | (exact GlobalTheory.Katz.rig_pull_natural_semi) | (intros; apply GlobalTheory.Katz.rig_pull_natural_semi  <;> assumption)
end

