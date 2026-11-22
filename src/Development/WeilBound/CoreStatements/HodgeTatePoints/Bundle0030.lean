import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
import Mathlib

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Twfunct
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twfunct

section General

variable {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {x : Spec (CommRingCat.of R) ⟶ S}

theorem exists_lift {T T' : Type} [CommGroup T] [CommGroup T'] (Γ : QFGroup R T) (Γ' : QFGroup R T')
    {N N' : ℕ} {i : Γ.G.left ⟶ G.left} {i' : Γ'.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) (h' : Γ'.IsTorsionAlong G x N' i') (hN : N ∣ N')
    (u : G ⟶ G) [IsMonHom u] : ∃ a : Γ.G ⟶ Γ'.G, a.left ≫ i' = i ≫ u.left := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨k, rfl⟩ := hN
  have hg' : (g ≫ u) ^ (N * k) = 1 := by
    rw [← MonObj.pow_comp, pow_mul, hg, one_pow, MonObj.one_comp]
  obtain ⟨a, ha⟩ := (h'.kernel Γ.G (g ≫ u)).1 hg'
  exact ⟨a, by rw [ha]; simp [g]⟩

theorem left_ext {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} (v w : Y ⟶ Γ.G.left) (h1 : v ≫ Γ.G.hom = w ≫ Γ.G.hom)
    (h2 : v ≫ i = w ≫ i) : v = w := by
  have := h.inj (Over.mk (w ≫ Γ.G.hom)) (Over.homMk v h1) (Over.homMk w rfl) h2
  exact congrArg (fun z => z.left) this

omit [IsDomain R] in
theorem valAt_comp {X Y : Scheme.{0}} (v : Spec (CommRingCat.of R) ⟶ X) (a : X ⟶ Y) (s : Γ(Y, ⊤)) :
    valAt v ⊤ le_top ((a.app ⊤).hom s) = valAt (v ≫ a) ⊤ le_top s :=
  Funct.valAt_pullback v a _ rfl ⊤ le_top le_top s

omit [IsDomain R] in
theorem valAt_specMap {B : Type} [CommRing B] {Y : Scheme.{0}} (π : R →+* B) (v : Spec (CommRingCat.of R) ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (Spec.map (CommRingCat.ofHom π) ≫ v) ⊤ le_top s = π (valAt v ⊤ le_top s) := by
  have h1 : ∀ {Z : Scheme.{0}} (w : Z ⟶ Y), w.appLE ⊤ ⊤ le_top = w.appTop := fun w =>
    w.appLE_eq_app
  simp only [valAt, h1]
  rw [Scheme.Hom.comp_appTop]
  have := congrArg (fun z => z.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom π))
  exact this

omit [IsDomain R] in
theorem pt_nsmul {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) (N : ℕ) :
    M.pt (N • e) = M.pt e ^ N := by
  induction N with
  | zero =>
    have := M.add 0 0
    rw [add_zero] at this
    simpa using (left_eq_mul.1 this)
  | succ k ih => rw [succ_nsmul, M.add, ih, pow_succ]

theorem exists_tan {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) :
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  let Q := R ⧸ Ideal.span {(N : R)}
  let q : R →+* Q := Ideal.Quotient.mk _
  let c : R →+* DualNumber Q := (algebraMap Q (DualNumber Q)).comp q
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom c))
  have hc : (dualMap q).comp (algebraMap R (DualNumber R)) = c := by
    ext r <;> simp [c, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : Over.mk (Y.hom ≫ x) ⟶ epsAt x := Over.homMk (Spec.map (CommRingCat.ofHom (dualMap q))) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hc])
  let k₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : q (N : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hc' : (dualMap q).comp (epsMul (N : R)) = c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun r => ?_
    ext <;> simp [c, dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, -map_natCast, hN]
  have hg : (k ≫ M.pt e) ^ N = 1 := by
    rw [← MonObj.comp_pow, ← pt_nsmul, ← MonObj.comp_one k₀]
    ext1
    rw [Over.comp_left, Over.comp_left, ← Nat.cast_smul_eq_nsmul R, M.smul, ← M.tan e]
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ Spec.map _ ≫ _
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc']
  obtain ⟨v, hv⟩ := (h.kernel Y (k ≫ M.pt e)).1 hg
  exact ⟨v.left, Over.w v, hv⟩

end General

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative
    (Submodule.mapQ _ _ φ.toIntLinearMap (by
      rintro _ ⟨a, rfl⟩
      exact ⟨φ a, (map_nsmul φ (p ^ n) a).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

theorem lev_surj {La : Type} [AddCommGroup La] (p n : ℕ) (t : LevGrp La p n) : ∃ a, lev p n a = t := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
  exact ⟨a, by simp [lev, ha]⟩

theorem lev_zero {La : Type} [AddCommGroup La] (p n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem finite_lev {La : Type} [AddCommGroup La] [Module.Finite ℤ La] {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast pow_ne_zero n hp)⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, (natCast_zsmul a (p ^ n)).symm⟩
  infer_instance

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)
  {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L)

theorem isDer_res (n : ℕ) (f : LevGrp La p (n + 1) → O) (g : LevGrp La p n → O) (w : Module.Dual O L)
    (hf : X.IsDer M (n + 1) f w) (hg : ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) : X.IsDer M n g w := by
  obtain ⟨s, hs, hw⟩ := hf
  obtain ⟨j, hj⟩ := exists_lift (X.Γ n) (X.Γ (n + 1)) (X.tors n) (X.tors (n + 1)) (pow_dvd_pow p n.le_succ) (𝟙 G)
  rw [Over.id_left, Category.comp_id] at hj
  refine ⟨(j.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · obtain ⟨a, rfl⟩ := lev_surj p n t
    have : ((X.Γ n).pt (lev p n a)).left ≫ j.left = ((X.Γ (n + 1)).pt (lev p (n + 1) (p • a))).left := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, Over.w, Over.w]
      · rw [Category.assoc, hj, X.compat]
    rw [valAt_comp, this, hs, hg]
  · obtain ⟨v, hv1, hv2, hv3⟩ := hw e
    obtain ⟨v', h1, h2⟩ := exists_tan (X.Γ n) (X.tors n) M e
    refine ⟨v', h1, h2, ?_⟩
    have hle : Ideal.span {((p ^ (n + 1) : ℕ) : O)} ≤ Ideal.span {((p ^ n : ℕ) : O)} :=
      Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (pow_dvd_pow p n.le_succ))
    let π := Ideal.Quotient.factor hle
    have : v' ≫ j.left = Spec.map (CommRingCat.ofHom (dualMap π)) ≫ v := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, Over.w, h1, hv1, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Category.assoc, Category.assoc, hj, h2, hv2, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
        congr 3
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap]
    have h0 : g 1 = f 1 := by simpa [lev_zero] using hg 0
    rw [valAt_comp, this, valAt_specMap, hv3, h0]
    ext <;> simp [π, dualMap]

theorem exists_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (hu : X.Induces u φ) (n : ℕ) :
    ∃ a : (X.Γ n).G ⟶ (X.Γ n).G, a.left ≫ X.i n = X.i n ≫ u.left ∧
      ∀ t, (X.Γ n).pt t ≫ a = (X.Γ n).pt (levMap p n φ t) := by
  obtain ⟨a, ha⟩ := exists_lift (X.Γ n) (X.Γ n) (X.tors n) (X.tors n) dvd_rfl u
  refine ⟨a, ha, fun t => ?_⟩
  obtain ⟨b, rfl⟩ := lev_surj p n t
  refine (X.tors n).inj _ _ _ ?_
  rw [levMap_lev, hu, Over.comp_left, Category.assoc, ha]

theorem isDer_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L) (hu : X.Induces u φ)
    (hd : M.IsDiffOf u dφ) (n : ℕ) (f : LevGrp La p n → O) (w : Module.Dual O L) (hf : X.IsDer M n f w) :
    X.IsDer M n (fun t => f (levMap p n φ t)) (w ∘ₗ dφ) := by
  obtain ⟨a, ha, hpt⟩ := exists_endo X u φ hu n
  obtain ⟨s, hs, hw⟩ := hf
  refine ⟨(a.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · rw [valAt_comp, ← Over.comp_left, hpt, hs]
  · obtain ⟨v, hv1, hv2, -⟩ := hw e
    obtain ⟨v', h1, h2, h3⟩ := hw (dφ e)
    refine ⟨v, hv1, hv2, ?_⟩
    have : v ≫ a.left = v' := by
      refine left_ext _ (X.tors n) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, h1, hv1]
      · rw [Category.assoc, ha, h2, hd e, ← Category.assoc, hv2, Over.comp_left, Category.assoc]
    rw [valAt_comp, this, h3]
    simp only [map_one, LinearMap.comp_apply]

set_option linter.unusedVariables false in
theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) := by
  intro p hpp C _ _ _ v O _ _ _ _ _ _ S _ G _ _ _ y La _ _ _ X L _ _ M
  refine ⟨isDer_res X M, fun u _ φ dφ hu hd n f g hg => ?_⟩
  obtain rfl : g = fun t => f (levMap p n φ t) := by
    funext t
    obtain ⟨b, rfl⟩ := lev_surj p n t
    rw [hg, levMap_lev]
  refine ⟨fun hf => ?_, isDer_endo X M u φ dφ hu hd n f⟩
  obtain ⟨a, -, hpt⟩ := exists_endo X u φ hu n
  have : Finite (LevGrp La p n) := finite_lev hpp.out.ne_zero n
  exact Funct.comp_mem_btOrder O _ _ _ _ a _ hpt f hf

end PositivityTheory.HtPt.Twfunct
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Twomega
section
noncomputable section

namespace PositivityTheory.HtPt.Twomega

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT

section Complete

variable {p : ℕ} {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem cong_iff {ι : Type} [Finite ι] (b : Module.Basis ι O M) (n : ℕ) (w w' : M) :
    (∃ u : M, w' = w + (p ^ n) • u) ↔ ∀ i, (p : O) ^ n ∣ b.equivFun w' i - b.equivFun w i := by
  constructor
  · rintro ⟨u, rfl⟩ i
    refine ⟨b.equivFun u i, ?_⟩
    rw [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, add_sub_cancel_left]
  · intro h
    choose c hc using h
    refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
    rw [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow,
      LinearEquiv.apply_symm_apply, ← hc, add_sub_cancel]

theorem smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔ (p : O) ^ n ∣ b - a := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_sub_comm]

theorem eq_zero_of_cong [Module.Free O M] [Module.Finite O M] (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
    (w : M) (h : ∀ n, ∃ u : M, w = 0 + (p ^ n) • u) : w = 0 := by
  let b := Module.Free.chooseBasis O M
  refine b.equivFun.injective (funext fun i => ?_)
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})).2 fun n => SModEq.symm ?_
  exact (smod_iff n _ _).2 ((cong_iff b n 0 w).1 (h n) i)

theorem exists_lim [Module.Free O M] [Module.Finite O M] (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
    (w : ℕ → M) (h : ∀ n, ∃ u : M, w (n + 1) = w n + (p ^ n) • u) :
    ∃ W : M, ∀ n, ∃ u : M, W = w n + (p ^ n) • u := by
  let b := Module.Free.chooseBasis O M
  have key : ∀ i, ∃ c : O, ∀ n, (p : O) ^ n ∣ c - b.equivFun (w n) i := by
    intro i
    have h1 : ∀ n, b.equivFun (w n) i ≡ b.equivFun (w (n + 1)) i
        [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] :=
      fun n => (smod_iff n _ _).2 ((cong_iff b n _ _).1 (h n) i)
    obtain ⟨c, hc⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => b.equivFun (w n) i)
      fun {m n} hmn => by
        induction n, hmn using Nat.le_induction with
        | base => rfl
        | succ n hmn ih =>
          exact ih.trans ((h1 n).mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)))
    exact ⟨c, fun n => (smod_iff n _ _).1 (hc n)⟩
  choose c hc using key
  exact ⟨b.equivFun.symm c, fun n => (cong_iff b n _ _).2 fun i => by
    rw [LinearEquiv.apply_symm_apply]; exact hc i n⟩

end Complete

variable {p : ℕ} {O : Type} [CommRing O] {La : Type} [AddCommGroup La]
  {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

theorem der_smul (n : ℕ) (r : O) (f : LevGrp La p n → O) (w : Module.Dual O L) (h : X.der n f w) :
    X.der n (r • f) (r • w) := by
  have := X.der_mul n _ _ _ _ (X.der_const n r) h
  rw [smul_zero, add_zero] at this
  exact this

theorem der_sub (n : ℕ) (f g : LevGrp La p n → O) (w w' : Module.Dual O L) (h : X.der n f w)
    (h' : X.der n g w') : X.der n (f - g) (w - w') := by
  have := X.der_add n _ _ _ _ h (der_smul X n (-1) g w' h')
  simpa only [neg_smul, one_smul, ← sub_eq_add_neg] using this

theorem der_of_mem_sq (n : ℕ) (f : X.A n) (hf : f ∈ BT.augIdeal (X.A n) ^ 2) : X.der n f.1 0 := by
  rw [sq] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨w, hw⟩ := X.der_ex n a.1 a.2
    obtain ⟨w', hw'⟩ := X.der_ex n b.1 b.2
    have ha0 : a.1 1 = 0 := ha
    have hb0 : b.1 1 = 0 := hb
    have := X.der_mul n _ _ _ _ hw hw'
    rw [ha0, hb0, zero_smul, zero_smul, add_zero] at this
    exact this
  · have := X.der_add n _ _ _ _ ha hb
    rw [add_zero] at this
    exact this

variable [Fact p.Prime] {X} {G : PDivGroup p O} {e : ∀ n, G.A n ≃ₐ[O] X.A n} {τ : La →+ G.Tate}

theorem counit_eq (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) :
    Bialgebra.counitAlgHom O (G.A n) a = (e n a).1 1 := by
  have h := hre.pt 0 n a
  rw [map_zero] at h
  exact h

theorem map_ker (hre : X.Realises G e τ) (n : ℕ) :
    (BT.augIdeal (X.A n)).comap (e n) = RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
  ext a
  rw [Ideal.mem_comap, OrderApi.mem_augIdeal, RingHom.mem_ker, counit_eq hre]

theorem mem_sq_iff (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) :
    a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 ↔ e n a ∈ BT.augIdeal (X.A n) ^ 2 := by
  have h : (RingHom.ker (Bialgebra.counitAlgHom O (G.A n))).map (e n) = BT.augIdeal (X.A n) := by
    rw [← map_ker hre, Ideal.map_comap_of_surjective _ (e n).surjective]
  rw [← h, ← Ideal.map_pow]
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro h1
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ (e n).surjective).1 h1
    rwa [← (e n).injective hab]

theorem dUnit_eq_zero_iff (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) :
    dUnit O a = 0 ↔ X.der n (e n a).1 0 := by
  rw [dUnit, AugCot.d_eq_zero_iff, mem_sq_iff hre, map_sub, AlgEquiv.commutes]
  set c := Bialgebra.counitAlgHom O (G.A n) a with hc
  have hc' : X.der n (algebraMap O (X.A n) c).1 0 := X.der_const n c
  constructor
  · intro h
    have := X.der_add n _ _ _ _ (der_of_mem_sq X n _ h) hc'
    simpa using this
  · intro h
    have h1 := der_sub X n _ _ _ _ h hc'
    rw [sub_zero] at h1
    refine X.der_zero n ⟨e n a - algebraMap O (X.A n) c, ?_⟩ h1
    rw [OrderApi.mem_augIdeal, hc, counit_eq hre]
    exact sub_self _

theorem dUnit_eq_iff (hre : X.Realises G e τ) (n : ℕ) (a b : G.A n) (w : Module.Dual O L)
    (h : X.der n (e n a).1 w) : dUnit O b = dUnit O a ↔ X.der n (e n b).1 w := by
  rw [← sub_eq_zero, dUnit, dUnit, ← map_sub]
  refine (dUnit_eq_zero_iff hre n (b - a)).trans ?_
  rw [map_sub]
  constructor
  · intro h1
    have := X.der_add n _ _ _ _ h1 h
    simpa using this
  · intro h1
    have := der_sub X n _ _ _ _ h1 h
    rw [sub_self] at this
    exact this

omit [Fact p.Prime] in
theorem exists_der (e : ∀ n, G.A n ≃ₐ[O] X.A n) (n : ℕ) (w : Module.Dual O L) :
    ∃ a : G.A n, X.der n (e n a).1 w := by
  obtain ⟨f, hf, h⟩ := X.der_onto n w
  exact ⟨(e n).symm ⟨f, hf⟩, by rwa [AlgEquiv.apply_symm_apply]⟩

def cls (e : ∀ n, G.A n ≃ₐ[O] X.A n) (n : ℕ) (w : Module.Dual O L) : Cot O (G.A n) :=
  dUnit O (exists_der e n w).choose

theorem dUnit_eq_cls (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) (w : Module.Dual O L) :
    dUnit O a = cls e n w ↔ X.der n (e n a).1 w :=
  dUnit_eq_iff hre n _ a w (exists_der e n w).choose_spec

theorem der_res (hre : X.Realises G e τ) (n : ℕ) (a : G.A (n + 1)) (w : Module.Dual O L)
    (h : X.der (n + 1) (e (n + 1) a).1 w) : X.der n (e n (G.res n a)).1 w :=
  X.der_res n _ _ w h (hre.res n a)

def toOmega (hre : X.Realises G e τ) : Module.Dual O L →ₗ[O] G.omega where
  toFun w := ⟨fun n => cls e n w, fun n => by
    obtain ⟨a, ha⟩ := exists_der e (n + 1) w
    change cotMap (G.res n) (cls e (n + 1) w) = cls e n w
    rw [← (dUnit_eq_cls hre _ a w).2 ha, cotMap_d, dUnit_eq_cls hre]
    exact der_res hre n a w ha⟩
  map_add' w w' := Subtype.ext (funext fun n => by
    obtain ⟨a, ha⟩ := exists_der e n w
    obtain ⟨b, hb⟩ := exists_der e n w'
    change cls e n (w + w') = cls e n w + cls e n w'
    rw [← (dUnit_eq_cls hre _ a w).2 ha, ← (dUnit_eq_cls hre _ b w').2 hb, dUnit, dUnit, ← map_add, eq_comm]
    refine (dUnit_eq_cls hre _ _ _).2 ?_
    rw [map_add]
    exact X.der_add n _ _ _ _ ha hb)
  map_smul' r w := Subtype.ext (funext fun n => by
    obtain ⟨a, ha⟩ := exists_der e n w
    change cls e n (r • w) = r • cls e n w
    rw [← (dUnit_eq_cls hre _ a w).2 ha, dUnit, ← map_smul, eq_comm]
    refine (dUnit_eq_cls hre _ _ _).2 ?_
    rw [map_smul]
    exact der_smul X n r _ _ ha)

theorem toOmega_val (hre : X.Realises G e τ) (w : Module.Dual O L) (n : ℕ) :
    (toOmega hre w).1 n = cls e n w := rfl

theorem toOmega_bijective (hO : IsAdicComplete (Ideal.span {(p : O)}) O) [Module.Free O L] [Module.Finite O L]
    (hre : X.Realises G e τ) : Function.Bijective (toOmega hre) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    refine eq_zero_of_cong hO w fun n => ?_
    have h0 : dUnit O (0 : G.A n) = 0 := map_zero _
    have h1 : cls e n w = 0 := congrArg (fun x : G.omega => x.1 n) hw
    exact (X.der_unique n _ 0 w ((dUnit_eq_zero_iff hre n 0).1 h0)).1
      ((dUnit_eq_cls hre n 0 w).1 (h0.trans h1.symm))
  · intro ω
    choose a ha using fun n => AugCot.d_surjective _ (ω.1 n)
    choose w hw using fun n => X.der_ex n (e n (a n)).1 (e n (a n)).2
    obtain ⟨W, hW⟩ := exists_lim hO w fun n => by
      refine (X.der_unique n _ _ _ (hw n)).1 ?_
      refine (dUnit_eq_iff hre n _ _ _ (der_res hre n _ _ (hw (n + 1)))).1 ?_
      rw [← cotMap_d, dUnit, dUnit, ha, ha]
      exact (ω.2 n).symm
    refine ⟨W, Subtype.ext (funext fun n => ?_)⟩
    rw [toOmega_val, ← ha, eq_comm]
    exact (dUnit_eq_cls hre n _ W).2 ((X.der_unique n _ _ _ (hw n)).2 (hW n))

end PositivityTheory.HtPt.Twomega

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Twomega.tower_omega : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) [Module.Free O L] [Module.Finite O L] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), ∃ j : G.omega ≃ₗ[O] Module.Dual O L, (∀ (χ : G.dual.Tate) n, X.der n (e n (charElem χ n)).1 (j (dlog G χ))) ∧ ∀ (φ : La →+ La) (dφ : L →ₗ[O] L) (f : G ⟶ G), X.Acts φ dφ → (∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) → ∀ w, j (omegaMap G G f w) = j w ∘ₗ dφ := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X _ _ G e τ hre
  let k := LinearEquiv.ofBijective _ (PositivityTheory.HtPt.Twomega.toOmega_bijective hO hre)
  have hk : ∀ (ω : G.omega) n, ω.1 n = PositivityTheory.HtPt.Twomega.cls e n (k.symm ω) := fun ω n =>
    congrArg (fun x : G.omega => x.1 n) (k.apply_symm_apply ω).symm
  refine ⟨k.symm, fun χ n => ?_, fun φ dφ f hφ hf ω => ?_⟩
  · exact (PositivityTheory.HtPt.Twomega.dUnit_eq_cls hre n _ _).1 (hk (dlog G χ) n)
  · rw [LinearEquiv.symm_apply_eq]
    refine Subtype.ext (funext fun n => ?_)
    obtain ⟨a, ha⟩ := PositivityTheory.HtPt.Twomega.exists_der e n (k.symm ω)
    rw [omegaMap_val, hk ω n, ← (PositivityTheory.HtPt.Twomega.dUnit_eq_cls hre n a _).2 ha, PDiv.cotMap_d]
    exact (PositivityTheory.HtPt.Twomega.dUnit_eq_cls hre n _ _).2 ((hφ n _ _ (hf n a)).2 _ ha)
end
end

