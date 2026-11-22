import Development.EtaleCohomology.TateTwists.Bundle0017
import Development.EtaleCohomology.TateTwists.Bundle0003
import Development.EtaleCohomology.TateTwists.Bundle0002
import Development.EtaleCohomology.TateTwists.Bundle0019
import Development.EtaleCohomology.TateTwists.Bundle0020

-- bundled from Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V1

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V (fun W k => Q W (k ≫ g))) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let R : ∀ ⦃Y⦄ ⦃f : Y ⟶ U⦄, S.arrows f → Sieve Y := fun Y f H => (hPQ Y f (hP Y f H)).choose
  refine ⟨Sieve.bind S.arrows R, Scheme.etaleTopology.bind_covering hS
    (fun Y f H => (hPQ Y f (hP Y f H)).choose_spec.1), ?_⟩
  rintro W _ ⟨Y, k, f, H, hk, rfl⟩
  exact (hPQ Y f (hP Y f H)).choose_spec.2 W k hk

theorem sec_res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (s : Sec F U) : Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sec_res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (s : Sec F U) :
    Sec.res (𝟙 U) s = s := by
  simp only [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (s : Sec F U) : Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  simp only [Sec.res, Sec.map]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    φ.hom.naturality]

theorem sx_res_comp {E : Spc} {p : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).res k = x.res (k ≫ g) := by
  simp only [Sx.res, op_comp, CategoryTheory.Functor.map_comp_apply]

theorem sx_res_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.res (𝟙 U) = x := by
  simp only [Sx.res, op_id, CategoryTheory.Functor.map_id_apply]

theorem units_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) =
      Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp [Scheme.Hom.comp_appTop]; rfl

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (s : Sec F U) : Sec.map ψ (Sec.map φ s) = Sec.map (φ ≫ ψ) s := rfl

theorem d_resGen (q : ℕ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res _ (tw q 1)).d 0 1) (resGen 1 ζ) = 0 := by
  have h : resι _ (tw q 1) ≫ (res _ (tw q 1)).d 0 1 = 0 := by
    have hc : (injectiveResolution (tw q 1)).ι'.f 0 ≫ (injectiveResolution (tw q 1)).cochainComplex.d 0 1 = 0 := by
      rw [(injectiveResolution (tw q 1)).ι'.comm 0 1]; simp
    exact (Category.assoc _ _ _).trans ((congrArg (fun f => _ ≫ f) hc).trans Limits.comp_zero)
  rw [resGen, sec_map_comp, h]
  simp [Sec.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  simp only [lineUnit, Sx.res]
  rw [NatTrans.naturality_apply]
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom (glMat ((L.app _).app (op U) x))) = _
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

noncomputable abbrev dkT (q : ℕ) (V : Scheme.{0}) (v : (Γ(V, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 1) V :=
  Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v)

theorem isUnit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

theorem kT_nat {q : ℕ} (hk : IsKum q (kumT q)) {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U)
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dkT q U v) = dkT q V (Units.map g.appTop.hom.toMonoidHom v) := by
  rw [dkT, sec_res_map, hk.1 V U g v hU]

theorem kT_pow {q : ℕ} (hk : IsKum q (kumT q)) {W : Scheme.{0}} (ζ : Prim q Γ(W, ⊤)) (w : (Γ(W, ⊤))ˣ) (a : ℕ) :
    ∀ w' : (Γ(W, ⊤))ˣ, (w' : Γ(W, ⊤)) = ζ.1 ^ a * w → dkT q W w' = dkT q W w := by
  induction a with
  | zero => intro w' h; have : w' = w := Units.ext (by simpa using h); subst this; rfl
  | succ n ih =>
    intro w' h
    have hu : IsUnit (ζ.1 ^ n * (w : Γ(W, ⊤))) :=
      isUnit_of_mul_isUnit_right (x := ζ.1) (by rw [← mul_assoc, ← pow_succ', ← h]; exact w'.isUnit)
    have e : (w' : Γ(W, ⊤)) = ζ.1 * (hu.unit : Γ(W, ⊤)) := by rw [IsUnit.unit_spec, h, pow_succ', mul_assoc]
    rw [dkT, hk.2 W ζ hu.unit w' e]
    simp only [Sec.map, map_add]
    have h0 := d_resGen q ζ
    simp only [Sec.map] at h0
    rw [h0, add_zero]
    exact ih hu.unit (IsUnit.unit_spec hu)

theorem indep {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) {V : Scheme.{0}} (hV : IsUnit (q : Γ(V, ⊤))) (v v' : (Γ(V, ⊤))ˣ)
    (h : v ^ q = v' ^ q) : dkT q V v = dkT q V v' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_bind ((hp q V).1 hV) ?_
  rintro W g ⟨ζ⟩
  have h1 : (v' * v⁻¹) ^ q = 1 := by rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  have hx : ((Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹) : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  refine loc_mono ((hp q W).2.2.1 ζ _ hx) ?_
  rintro W' k ⟨a, ha⟩
  rw [kT_nat hk hV, kT_nat hk hV]
  have hx' : ((Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹)) : (Γ(W', ⊤))ˣ) : Γ(W', ⊤))
      = (Prim.map k.appTop.hom ζ).1 ^ a := ha
  have e : ((Units.map (k ≫ g).appTop.hom.toMonoidHom v' : (Γ(W', ⊤))ˣ) : Γ(W', ⊤)) =
      (Prim.map k.appTop.hom ζ).1 ^ a * (Units.map (k ≫ g).appTop.hom.toMonoidHom v : (Γ(W', ⊤))ˣ) := by
    rw [← units_map_comp, ← units_map_comp, ← hx', ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
  exact (kT_pow hk _ _ a _ e).symm

def Q (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) (s : Sec ((res _ (tw q 1)).X 1) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = lineUnit L (x.res g) → Sec.res g s = dkT q V v

theorem Q_res {q : ℕ} {E : Spc} {L : E ⟶ ofCat (glCat 1)} {V U : Scheme.{0}} {x : Sx E 1 U} {s} (hQ : Q q L x s)
    (g : V ⟶ U) : Q q L (x.res g) (Sec.res g s) := by
  intro W k v hv
  rw [sec_res_comp]
  exact hQ W (k ≫ g) v (by rwa [← sx_res_comp])

theorem Q_uniq {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} {L : E ⟶ ofCat (glCat 1)} {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {x : Sx E 1 U} {s s'}
    (hQ : Q q L x s) (hQ' : Q q L x s') : s = s' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) U).1
  refine loc_mono ((hp q U).2.2.2 hU (lineUnit L x)) ?_
  rintro V g ⟨v, hv⟩
  have hv' : v ^ q = lineUnit L (x.res g) := by rw [lineUnit_res]; exact hv
  rw [hQ V g v hv', hQ' V g v hv']

theorem Q_ex {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (x : Sx E 1 U) :
    ∃ s, Q q L x s := by
  obtain ⟨S, hS, hr⟩ := (hp q U).2.2.2 hU (lineUnit L x)
  choose vs hvs using hr
  obtain ⟨s, hs'⟩ := (hs (ZMod q) ((res _ (tw q 1)).X 1) U).2 S hS (fun V g hg => dkT q V (vs V g hg)) (by
    intro V W g k hg
    rw [kT_nat hk (isUnit_res hU g)]
    apply indep hp hk hs (isUnit_res hU (k ≫ g))
    rw [← map_pow, hvs V g hg, units_map_comp, hvs W (k ≫ g) _])
  refine ⟨s, fun V g v hv => ?_⟩
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_mono (P := fun W h => S.arrows (h ≫ g))
    ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => hh⟩ ?_
  intro W h hh
  rw [sec_res_comp, hs' W (h ≫ g) hh, kT_nat hk (isUnit_res hU g)]
  apply indep hp hk hs (isUnit_res hU (h ≫ g))
  rw [hvs, ← map_pow, hv, lineUnit_res, units_map_comp]

end LateralTheory.EtaleFoundations.V1

open LateralTheory.EtaleFoundations.V1 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists)
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeOneValue := by
  classical
  intro q _ E L hi
  have hU : ∀ (U : Scheme.{0}) (x : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.face 0⟩
  have hex : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ s, Q q L x s := fun U x => Q_ex hp (hk q) hs L (hU U x) x
  refine ⟨fun U x => (hex U x).choose, fun V U g x =>
    Q_uniq hp hs (hU V (x.res g)) (Q_res (hex U x).choose_spec g) (hex V (x.res g)).choose_spec, fun U x v hv => ?_⟩
  have h := (hex U x).choose_spec U (𝟙 U) v (by rwa [sx_res_id])
  rwa [sec_res_id] at h
end

-- bundled from Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeTwoValueOfRootsKum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V2

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def KumTEx : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def SecGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h⟩ := hP
  obtain ⟨T, hT, h'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h V g hg.1, h' V g hg.2⟩⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, h'⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h' V g hg)⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp]; rfl

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

theorem umap_id {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : Units.map (Scheme.Hom.appTop (𝟙 U)).hom.toMonoidHom u = u := by
  ext; simp

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (h : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  have := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
  simpa using this

theorem glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) = Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem det_gmap {V U : Scheme.{0}} (g : V ⟶ U) (m : GL (Fin 1) Γ(U, ⊤)) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom m) = Units.map g.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  simp [Matrix.GeneralLinearGroup.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  have := ConcreteCategory.congr_hom ((L.app (op (SimplexCategory.mk 1))).naturality g.op) x
  simp only [ConcreteCategory.comp_apply] at this
  rw [this, glMat_res, det_gmap]

noncomputable def fv (q : ℕ) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  kumT q U v + kumT q U w - kumT q U (v * w)

theorem kumT_pow (hK : KumTEx) (q : ℕ) [NeZero q] {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    ∀ (a : ℕ) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 ^ a * v → kumT q U w = kumT q U v + a • resGen 1 ζ := by
  intro a
  induction a with
  | zero => intro v w h; have : w = v := Units.ext (by simpa using h); subst this; simp
  | succ a ih =>
    intro v w h
    have hu : IsUnit (ζ.1 ^ (a + 1)) := by
      rw [show ζ.1 ^ (a + 1) = (w : Γ(U, ⊤)) * ((v⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) by rw [h, mul_assoc]; simp]
      exact (w * v⁻¹).isUnit
    have hz : IsUnit ζ.1 := (isUnit_pow_iff (Nat.succ_ne_zero a)).1 hu
    let m : (Γ(U, ⊤))ˣ := hz.unit ^ a * v
    have hm : kumT q U m = kumT q U v + a • resGen 1 ζ := ih v m (by simp [m])
    have hw : kumT q U w = kumT q U m + resGen 1 ζ := (hK q).2 U ζ m w (by rw [h]; simp [m, pow_succ']; ring)
    rw [hw, hm, succ_nsmul, add_assoc]

theorem res_fv (hK : KumTEx) (q : ℕ) [NeZero q] {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v w : (Γ(U, ⊤))ˣ) :
    Sec.res g (fv q U v w) = fv q V (Units.map g.appTop.hom.toMonoidHom v) (Units.map g.appTop.hom.toMonoidHom w) := by
  have e : ∀ a b c : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (a + b - c) = Sec.res g a + Sec.res g b - Sec.res g c := by
    intro a b c; simp [Sec.res]
  unfold fv
  rw [e, (hK q).1 V U g v hq, (hK q).1 V U g w hq, (hK q).1 V U g (v * w) hq, map_mul]

theorem umap_root {q : ℕ} {W V : Scheme.{0}} (h : W ⟶ V) (ζ : Prim q Γ(V, ⊤)) (v v' : (Γ(V, ⊤))ˣ) (a : ℕ)
    (ha : h.appTop.hom ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a) :
    ((Units.map h.appTop.hom.toMonoidHom v' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ a * Units.map h.appTop.hom.toMonoidHom v := by
  have : (v' : Γ(V, ⊤)) = ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) * v := by simp
  show h.appTop.hom (v' : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a * h.appTop.hom v
  rw [this, map_mul, ha]

theorem indepA (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤))
    (hq : IsUnit (q : Γ(V, ⊤))) (v v' w w' : (Γ(V, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q V v w = fv q V v' w' := by
  have hx : (((v' * v⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hv, inv_pow, mul_inv_cancel]; rfl
  have hy : (((w' * w⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hw, inv_pow, mul_inv_cancel]; rfl
  apply (hG _ _ V).1
  refine loc_mono (loc_and ((hP q V).2.2.1 ζ _ hx) ((hP q V).2.2.1 ζ _ hy)) ?_
  rintro W h ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [res_fv hK q h hq, res_fv hK q h hq]
  have h1 := umap_root h ζ v v' a ha
  have h2 := umap_root h ζ w w' b hb
  have h3 : ((Units.map h.appTop.hom.toMonoidHom v' * Units.map h.appTop.hom.toMonoidHom w' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ (a + b) * ((Units.map h.appTop.hom.toMonoidHom v * Units.map h.appTop.hom.toMonoidHom w : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) := by
    rw [Units.val_mul, h1, h2, Units.val_mul, pow_add]; ring
  unfold fv
  rw [kumT_pow hK q _ a _ _ h1, kumT_pow hK q _ b _ _ h2, kumT_pow hK q _ (a + b) _ _ h3, add_nsmul]
  abel

theorem indepB (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (v v' w w' : (Γ(U, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q U v w = fv q U v' w' := by
  apply (hG _ _ U).1
  refine loc_mono ((hP q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  rw [res_fv hK q g hq, res_fv hK q g hq]
  exact indepA hP hK hG q ζ (unit_res g hq) _ _ _ _ (by rw [← map_pow, ← map_pow, hv]) (by rw [← map_pow, ← map_pow, hw])

def Good (q : ℕ) (U : Scheme.{0}) (u1 u2 : (Γ(U, ⊤))ˣ) (a : Sec ((res _ (tw q 1)).X 0) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u1 →
    w ^ q = Units.map g.appTop.hom.toMonoidHom u2 → Sec.res g a = fv q V v w

theorem good_exists (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (u1 u2 : (Γ(U, ⊤))ˣ) : ∃ a, Good q U u1 u2 a := by
  obtain ⟨S, hS, hS'⟩ := loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => fv q V (hS' V g hg).1.choose (hS' V g hg).2.choose
  obtain ⟨a, ha⟩ := (hG _ _ U).2 S hS s (by
    intro V W g k hg
    simp only [s]
    rw [res_fv hK q k (unit_res g hq)]
    apply indepB hP hK hG q (unit_res (k ≫ g) hq)
    · rw [← map_pow, (hS' V g hg).1.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).1.choose_spec]
    · rw [← map_pow, (hS' V g hg).2.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).2.choose_spec])
  refine ⟨a, fun V g v w hv hw => ?_⟩
  apply (hG _ _ V).1
  refine ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩
  show Sec.res k (Sec.res g a) = Sec.res k (fv q V v w)
  rw [res_comp, ha W (k ≫ g) hk, res_fv hK q k (unit_res g hq)]
  apply indepB hP hK hG q (unit_res (k ≫ g) hq)
  · rw [(hS' W (k ≫ g) hk).1.choose_spec, ← map_pow, hv, umap_comp]
  · rw [(hS' W (k ≫ g) hk).2.choose_spec, ← map_pow, hw, umap_comp]

theorem good_unique (hP : PrimLoc) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) {u1 u2 : (Γ(U, ⊤))ˣ} {a b : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) (hb : Good q U u1 u2 b) : a = b := by
  apply (hG _ _ U).1
  refine loc_mono (loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  rw [ha V g v w hv hw, hb V g v w hv hw]

theorem good_res (q : ℕ) {V U : Scheme.{0}} (g : V ⟶ U) {u1 u2 : (Γ(U, ⊤))ˣ} {a : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) :
    Good q V (Units.map g.appTop.hom.toMonoidHom u1) (Units.map g.appTop.hom.toMonoidHom u2) (Sec.res g a) := by
  intro W k v w hv hw
  rw [res_comp]
  exact ha W (k ≫ g) v w (by rw [hv, umap_comp]) (by rw [hw, umap_comp])

end LateralTheory.EtaleFoundations.V2

open LateralTheory.EtaleFoundations.V2 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeTwoValue := by
  intro q _ E L hi
  have hq : ∀ (U : Scheme.{0}) (x : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.sub 0 0 (by omega)⟩
  refine ⟨fun U x => pick (Good q U (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))), ?_, ?_⟩
  · intro V U g x
    have e1 : lineUnit L ((x.res g).sub 0 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 0 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have e2 : lineUnit L ((x.res g).sub 1 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 1 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have h1 := good_res q g (pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))))
    rw [← e1, ← e2] at h1
    exact good_unique hP hG q (hq V (x.res g)) h1 (pick_spec (good_exists hP hK hG q (hq V (x.res g)) _ _))
  · intro U x v w hv hw
    have := pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega))))
      U (𝟙 U) v w (by rw [umap_id]; exact hv) (by rw [umap_id]; exact hw)
    rwa [res_id] at this
end

-- bundled from Development.EtaleCohomology.TateTwists.KumUniqPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def uniq_prim_loc : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sections_unique_of_local_agreement : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def uniq_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

theorem sec_neg_eq (q : ℕ) [NeZero q] (s : ℤ) (hs : s < 0) (U : Scheme.{0})
    (a b : Sec ((res _ (tw q 1)).X s) U) : a = b := by
  have h0 : IsZero ((res _ (tw q 1)).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h1 : IsZero (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map_isZero h0)
  have : Subsingleton (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    (ModuleCat.isZero_iff_subsingleton).mp h1
  exact Subsingleton.elim a b

theorem root_res (q : ℕ) (X U V : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ)
    (hv : v ^ q = Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u)) :
    v ^ q = Units.map (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X).appTop.hom.toMonoidHom u := by
  have e : (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X) = g ≫ x := rfl
  rw [hv, e]; ext; simp
  rfl

theorem kum_uniq_of (hl : uniq_prim_loc) (hg : sections_unique_of_local_agreement) (hb : uniq_ev_basic) : kum_uniq := by
  intro q _ X u hq γ γ' h h'
  have key : γ = γ' := by
    apply Subtype.ext
    apply (hb (ZMod q)).2.2.1
    intro p s hs U x
    rcases p with _ | _ | p
    · have hs' : s = 1 := by omega
      subst hs'
      have hqU : IsUnit ((q : ℕ) : Γ(U, ⊤)) := by
        have := hq.map x.appTop.hom
        simpa using this
      obtain ⟨S, hS, hP⟩ := (hl q U).2.2.2 hqU (Units.map x.appTop.hom.toMonoidHom u)
      apply (hg (ZMod q) _ U).1
      refine ⟨S, hS, fun V g hgS => ?_⟩
      obtain ⟨v, hv⟩ := hP V g hgS
      rw [(hb (ZMod q)).2.1, (hb (ZMod q)).2.1]
      have hv' := root_res q X U V u x g v hv
      rw [h.2 V _ v hv', h'.2 V _ v hv']
    · have hs' : s = 0 := by omega
      subst hs'
      rw [h.1 U x, h'.1 U x]
    · exact sec_neg_eq q s (by omega) U _ _
  rw [key]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TPaCpushIdPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_id_of : t_pa_cpush_id := by
  intro R _ E I n x
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp a (Cocycle.ofHom (𝟙 I)) (add_zero n)) = CohomologyClass.mk a
  congr 1
  apply Cocycle.ext
  simp [zcomp]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TPaPrecompPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem pa_sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)
  simpa using this.symm

theorem pa_sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem t_pa_precomp_of : t_pa_precomp := by
  intro R _ I I' J K u μ
  refine ⟨⟨fun U s t w h => (μ.mul U s t w h).comp ((u.f s).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    simp only [LinearMap.comp_apply]
    exact (μ.nat g s t w h _ b).trans (by rw [pa_sec_res_map])
  · intro U s t w h a b
    simp only [LinearMap.comp_apply]
    rw [μ.leibniz]
    congr 2
    rw [← pa_sec_map_comp, u.comm]; rfl
  · intro U s t w h a b
    rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensExPfLoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

theorem tt_sheafify_locSurj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : ((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.obj (op U)) :
    Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology.{0} P).app (op V)).hom x =
      (((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.map g.op).hom y :=
  ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) y,
    fun _ _ ⟨x, hx⟩ => ⟨x, hx⟩⟩

theorem tt_sheafify_locInj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (x : P.obj (op U)) (hx : ((toSheafify Scheme.etaleTopology.{0} P).app (op U)).hom x = 0) :
    Loc U fun _ g => (P.map g.op).hom x = 0 := by
  refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) x 0
    (by simpa using hx), fun _ _ h => ?_⟩
  simpa using h

end LateralTheory.EtaleFoundations
end

