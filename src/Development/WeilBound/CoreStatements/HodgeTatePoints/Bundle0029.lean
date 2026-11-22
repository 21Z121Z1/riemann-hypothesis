import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.DualLattices.PowMemCarrier

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MhTorusA
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

open scoped CategoryTheory.Obj

section Bridge
variable {S' S : Scheme.{0}} (x : S' ⟶ S) (G : Over S)

def toPull {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) : Y ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift g.left Y.hom (by simpa using Over.w g)) (pullback.lift_snd _ _ _)

theorem toPull_fst {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    (toPull x G g).left ≫ pullback.fst G.hom x = g.left := pullback.lift_fst _ _ _

variable {x G} in
theorem hom_ext_pull {Y : Over S'} {y z : Y ⟶ (Over.pullback x).obj G}
    (h : y.left ≫ pullback.fst G.hom x = z.left ≫ pullback.fst G.hom x) : y = z := by
  ext
  refine pullback.hom_ext h ?_
  have h1 := Over.w y
  have h2 := Over.w z
  simp only [Over.pullback_obj_hom] at h1 h2
  rw [h1, h2]

theorem toPull_eq {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    toPull x G g = toPull x _ (𝟙 (Over.mk (Y.hom ≫ x))) ≫ (Over.pullback x).map g := by
  apply hom_ext_pull
  have h1 : ((Over.pullback x).map g).left ≫ pullback.fst G.hom x = pullback.fst _ x ≫ g.left :=
    pullback.lift_fst _ _ _
  have h2 := toPull_fst x _ (𝟙 (Over.mk (Y.hom ≫ x)))
  rw [toPull_fst, Over.comp_left, Category.assoc, h1, ← Category.assoc, h2]
  simp

def toPullHom [GrpObj G] (Y : Over S') : (Over.mk (Y.hom ≫ x) ⟶ G) →* (Y ⟶ (Over.pullback x).obj G) where
  toFun := toPull x G
  map_one' := by
    rw [toPull_eq, Functor.map_one, MonObj.comp_one]
  map_mul' g h := by
    rw [toPull_eq, toPull_eq x G g, toPull_eq x G h, Functor.map_mul, MonObj.comp_mul]

def ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : Over.mk (Y.hom ≫ x) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h1 := Over.w y
    simp only [Over.pullback_obj_hom] at h1
    simp [pullback.condition, reassoc_of% h1])

theorem toPull_ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : toPull x G (ofPull x G y) = y := by
  apply hom_ext_pull
  rw [toPull_fst]
  rfl

end Bridge

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def torFst (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    (splitTorus S X).left ⟶ Spec (CommRingCat.of (AddMonoidAlgebra ZU.{0} X)) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

def chi {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) : Multiplicative X →* Γ(Y, ⊤) :=
  (pb (g ≫ torFst S X)).toMonoidHom.comp (AddMonoidAlgebra.of ZU.{0} X)

theorem chi_apply {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi g x = pb (g ≫ torFst S X) (AddMonoidAlgebra.single x.toAdd 1) := rfl

theorem chi_comp {Y Y' : Scheme.{0}} (f : Y' ⟶ Y) (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi (f ≫ g) x = f.appTop (chi g x) := by
  rw [chi_apply, chi_apply, Category.assoc, pb_comp]

theorem chi_ext {Y : Scheme.{0}} {g h : Y ⟶ (splitTorus S X).left}
    (w : g ≫ (splitTorus S X).hom = h ≫ (splitTorus S X).hom) (e : ∀ x, chi g x = chi h x) : g = h := by
  refine pullback.hom_ext (f := (splitTorusAff ZU X).hom) (g := toZ S) ?_ w
  refine pb_ext (j := g ≫ torFst S X) (j' := h ≫ torFst S X) (RingHom.congr_fun ?_)
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun m => e (Multiplicative.ofAdd m)
  have e1 : ∀ k : Y ⟶ (splitTorus S X).left, pb (k ≫ torFst S X) (AddMonoidAlgebra.single 0 r) = pb (toZ Y) r := by
    intro k
    refine (pb_spec (k ≫ torFst S X) (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)) r).symm.trans ?_
    congr 2
    exact specULiftZIsTerminal.hom_ext _ _
  rw [e1, e1]

theorem exists_chi (Y : Over S) (c : Multiplicative X →* Γ(Y.left, ⊤)) :
    ∃ g : Y ⟶ splitTorus S X, ∀ x, chi g.left x = c x := by
  obtain ⟨j, hj⟩ := exists_pb (AddMonoidAlgebra.liftNCRingHom (k := ZU.{0}) (pb (toZ Y.left)) c
    fun _ _ => Commute.all _ _)
  refine ⟨Over.homMk (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), fun x => ?_⟩
  have e : (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) ≫ torFst S X = j := pullback.lift_fst _ _ _
  refine (congrArg (fun k => pb k (AddMonoidAlgebra.single x.toAdd 1)) e).trans ?_
  rw [hj, AddMonoidAlgebra.liftNCRingHom_single, map_one, _root_.one_mul]
  rfl

theorem pb_mul_aff {Y : Over (Spec ZU.{0})} (g h : Y ⟶ splitTorusAff ZU X) (x : X) :
    pb (A := AddMonoidAlgebra ZU.{0} X) (g * h).left (AddMonoidAlgebra.single x 1) =
      pb (A := AddMonoidAlgebra ZU.{0} X) g.left (AddMonoidAlgebra.single x 1) *
        pb (A := AddMonoidAlgebra ZU.{0} X) h.left (AddMonoidAlgebra.single x 1) := by
  let A := AddMonoidAlgebra ZU.{0} X
  let q : Y.left ⟶ Spec (CommRingCat.of (A ⊗[ZU.{0}] A)) := (lift g h).left ≫ (pullbackSpecIso ZU.{0} A A).hom
  have e0 : (g * h).left = q ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A : A →+* A ⊗[ZU.{0}] A)) := rfl
  have e1 : q ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = g.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A)).trans
      (congrArg (·.left) (lift_fst g h)))
  have e2 : q ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom Algebra.TensorProduct.includeRight)) = h.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A)).trans
      (congrArg (·.left) (lift_snd g h)))
  rw [e0, ← e1, ← e2, pb_spec, pb_spec, pb_spec, ← map_mul]
  congr 1
  simp [A, AddMonoidAlgebra.comul_single]

theorem chi_mul {Y : Over S} (g h : Y ⟶ splitTorus S X) (x : Multiplicative X) :
    chi (g * h).left x = chi g.left x * chi h.left x := by
  let g' := ofPull (toZ S) (splitTorusAff ZU X) g
  let h' := ofPull (toZ S) (splitTorusAff ZU X) h
  have e : g * h = toPull (toZ S) (splitTorusAff ZU X) (g' * h') :=
    ((map_mul (toPullHom (toZ S) (splitTorusAff ZU X) Y) g' h').trans
      (congrArg₂ (· * ·) (toPull_ofPull _ _ g) (toPull_ofPull _ _ h))).symm
  have e' : (g * h).left ≫ torFst S X = (g' * h').left := by
    rw [e]
    exact toPull_fst _ _ _
  rw [chi_apply, e']
  exact pb_mul_aff g' h' x.toAdd

theorem chi_one (Y : Over S) (x : Multiplicative X) : chi (1 : Y ⟶ splitTorus S X).left x = 1 := by
  have h := chi_mul (1 : Y ⟶ splitTorus S X) 1 x
  rw [_root_.mul_one] at h
  have hu : IsUnit (chi (1 : Y ⟶ splitTorus S X).left x) := (Group.isUnit x).map _
  exact (hu.mul_eq_left.1 h.symm)

theorem chi_pow {Y : Over S} (g : Y ⟶ splitTorus S X) (x : Multiplicative X) (n : ℕ) :
    chi (g ^ n).left x = chi g.left x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, chi_one]
  | succ n ih => rw [pow_succ, pow_succ, chi_mul, ih]

theorem pow_eq_one_iff_chi {Y : Over S} (g : Y ⟶ splitTorus S X) (n : ℕ) :
    g ^ n = 1 ↔ ∀ x, chi g.left x ^ n = 1 := by
  refine ⟨fun h x => by rw [← chi_pow, h, chi_one], fun h => Over.OverMorphism.ext (chi_ext ?_ fun x => ?_)⟩
  · exact (Over.w _).trans (Over.w _).symm
  · rw [chi_pow, h, chi_one]

end PositivityTheory.HtPt.Mh
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
section
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X N Q : Type} [AddCommGroup X] [AddCommGroup N] [AddCommGroup Q]

lemma map_res_eq (M : Submodule R (N → C)) (ι : X →+ N) (K : AddSubgroup N) (e : X ≃+ K)
    (he : ∀ x, (e x : N) = ι x) :
    M.map (LinearMap.funLeft R C ι) =
      (M.map (resK (R := R) K)).map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (X → C)) := by
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro g
  funext x
  show g (ι x) = g (e x)
  rw [he]

lemma comap_quo_eq (M : Submodule R (N → C)) (ψ : N →+ Q) (K : AddSubgroup N) (e : Q ≃+ N ⧸ K)
    (he : ∀ x, e (ψ x) = (x : N ⧸ K)) :
    M.comap (LinearMap.funLeft R C ψ) =
      (M.comap (pullQ (R := R) K)).map (pbE (C := C) (R := R) e : (N ⧸ K → C) →ₗ[R] (Q → C)) := by
  ext g
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  have : pullQ (R := R) K ((pbE (C := C) (R := R) e).symm g) = LinearMap.funLeft R C ψ g := by
    funext x
    show (pbE (C := C) (R := R) e).symm g (x : N ⧸ K) = g (ψ x)
    rw [LinearEquiv.funCongrLeft_symm]
    show g (e.symm (x : N ⧸ K)) = g (ψ x)
    rw [← he, AddEquiv.symm_apply_apply]
  rw [this]

lemma exists_subEquiv (ι : X →+ N) (hι : Function.Injective ι) (K : AddSubgroup N)
    (hK : ι.range = K) : ∃ e : X ≃+ K, ∀ x, (e x : N) = ι x := by
  subst hK
  exact ⟨AddMonoidHom.ofInjective hι, fun _ => rfl⟩

lemma exists_quoEquiv (ψ : N →+ Q) (hψ : Function.Surjective ψ) (K : AddSubgroup N)
    (hK : K = ψ.ker) : ∃ e : Q ≃+ N ⧸ K, ∀ x, e (ψ x) = (x : N ⧸ K) := by
  subst hK
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm, fun x => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  rfl

lemma invFun_eq (M : Submodule R (N → C)) (ψ : N →+ Q) (hψ : Function.Surjective ψ)
    (K : AddSubgroup N) (hK : ∀ x, x ∈ K ↔ ψ x = 0) :
    invFun M K = (M.comap (LinearMap.funLeft R C ψ)).map (LinearMap.funLeft R C ψ) := by
  ext g
  constructor
  · rintro ⟨hg, hinv⟩
    have h : LinearMap.funLeft R C ψ (fun c => g (Function.surjInv hψ c)) = g := by
      funext x
      show g (Function.surjInv hψ (ψ x)) = g x
      have hk : Function.surjInv hψ (ψ x) - x ∈ K := by
        rw [hK, map_sub, Function.surjInv_eq hψ, sub_self]
      have := hinv x _ hk
      rwa [add_sub_cancel] at this
    exact ⟨_, by show LinearMap.funLeft R C ψ _ ∈ M; rw [h]; exact hg, h⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q (ψ (x + k)) = q (ψ x)
    rw [map_add, (hK k).1 hk, add_zero]

lemma aug_pull (φ : X →+ N) (M : Submodule R (N → C)) (M' : Submodule R (X → C))
    (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C} (hg : g ∈ augIdeal M) :
    LinearMap.funLeft R C φ g ∈ augIdeal M' := by
  rw [mem_aug] at hg ⊢
  refine ⟨h g hg.1, ?_⟩
  show g (φ 0) = 0
  rw [map_zero, hg.2]

lemma sq_pull (φ : X →+ N) (M : Submodule R (N → C)) (M' : Submodule R (X → C))
    (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    LinearMap.funLeft R C φ g ∈ sqIdeal (augIdeal M') := by
  have h' : (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C φ) ≤ sqIdeal (augIdeal M') := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro s ⟨f, hf, f', hf', rfl⟩
    exact Submodule.subset_span ⟨_, aug_pull φ M M' h hf, _, aug_pull φ M M' h hf', rfl⟩
  exact h' (Submodule.mem_map_of_mem hg)

variable {v : Valuation C NNReal}

theorem exists_res (hv : v.Integers R) [Fintype N] [DecidableEq N] [Fintype X] [DecidableEq X]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N) (hι : Function.Injective ι) :
    ∃ AK : HopfOrder (C := C) R X, AK.carrier = AA.carrier.map (LinearMap.funLeft R C ι) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K, ι.range = K := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := exists_subEquiv ι hι K hK
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨AK, hAK⟩, -⟩ := ReciprocityTheory.PGsh.L2.h2 C R v hv N K AA
  refine ⟨hopfPull e AK, ?_⟩
  rw [map_res_eq _ ι _ e he, ← hAK]
  rfl

theorem exists_quo (hv : v.Integers R) [Fintype N] [DecidableEq N] [Fintype Q] [DecidableEq Q]
    (AA : HopfOrder (C := C) R N) (ψ : N →+ Q) (hψ : Function.Surjective ψ) :
    ∃ AQ : HopfOrder (C := C) R Q, AQ.carrier = AA.carrier.comap (LinearMap.funLeft R C ψ) := by
  classical
  obtain ⟨e, he⟩ := exists_quoEquiv ψ hψ ψ.ker rfl
  have : Fintype (N ⧸ ψ.ker) := Fintype.ofFinite _
  obtain ⟨-, ⟨AQ, hAQ⟩, -⟩ := ReciprocityTheory.PGsh.L2.h2 C R v hv N ψ.ker AA
  refine ⟨hopfPull e AQ, ?_⟩
  rw [comap_quo_eq _ ψ _ e he, ← hAQ]
  rfl

theorem colen_ses [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype N] [DecidableEq N]
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N) (hι : Function.Injective ι)
    (ψ : N →+ Q) (hψ : Function.Surjective ψ) (hex : ι.range = ψ.ker) (c cQ cK : NNReal)
    (hc : HasColen R v AA.carrier c)
    (hQ : HasColen R v (AA.carrier.comap (LinearMap.funLeft R C ψ)) cQ)
    (hK : HasColen R v (AA.carrier.map (LinearMap.funLeft R C ι)) cK) :
    c = cQ ^ Fintype.card X * cK ^ Fintype.card Q := by
  classical
  obtain ⟨K, hKd⟩ : ∃ K, ι.range = K := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := exists_subEquiv ι hι K hKd
  obtain ⟨e', he'⟩ := exists_quoEquiv ψ hψ K (hKd ▸ hex)
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨-, -, h3iii, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  rw [map_res_eq _ ι _ e he] at hK
  rw [comap_quo_eq _ ψ _ e' he'] at hQ
  have hK' := hasColen_map v e.symm _ _ hK
  have hQ' := hasColen_map v e'.symm _ _ hQ
  rw [map_pbE_symm] at hK' hQ'
  rw [Fintype.card_congr e.toEquiv, Fintype.card_congr e'.toEquiv]
  exact h3iii c cQ cK hc hQ' hK'

theorem om_exact [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N)
    (ψ : N →+ Q) (hψ : Function.Surjective ψ) (hι : Function.Injective ι) (hex : ι.range = ψ.ker)
    (g : N → C) (hg : g ∈ augIdeal AA.carrier)
    (hr : LinearMap.funLeft R C ι g ∈
      sqIdeal (augIdeal (AA.carrier.map (LinearMap.funLeft R C ι)))) :
    ∃ b ∈ augIdeal (AA.carrier.comap (LinearMap.funLeft R C ψ)),
      g - LinearMap.funLeft R C ψ b ∈ sqIdeal (augIdeal AA.carrier) := by
  classical
  obtain ⟨e, he⟩ := exists_subEquiv ι hι _ rfl
  obtain ⟨e', he'⟩ := exists_quoEquiv ψ hψ ι.range hex
  have : Fintype (N ⧸ ι.range) := Fintype.ofFinite _
  obtain ⟨-, -, -, h3iv⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N ι.range AA
  have hres : ∀ f : N → C, LinearMap.funLeft R C (e.symm : ι.range →+ X)
      (LinearMap.funLeft R C ι f) = resK (R := R) ι.range f := by
    intro f
    funext k
    show f (ι (e.symm k)) = f k
    rw [← he, AddEquiv.apply_symm_apply]
  have h1 := sq_pull (e.symm : ι.range →+ X) _ (AA.carrier.map (resK (R := R) ι.range))
    (by rintro _ ⟨f, hf, rfl⟩; rw [hres]; exact ⟨f, hf, rfl⟩) hr
  rw [hres, sq_eq_mul] at h1
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (h3iv g hg h1)
  obtain ⟨b, hb, rfl⟩ := hu
  have hp : ∀ b : N ⧸ ι.range → C, LinearMap.funLeft R C ψ
      (LinearMap.funLeft R C (e' : Q →+ N ⧸ ι.range) b) = pullQ (R := R) ι.range b := by
    intro b
    funext x
    show b (e' (ψ x)) = b x
    rw [he']
  refine ⟨LinearMap.funLeft R C (e' : Q →+ N ⧸ ι.range) b, aug_pull _ _ _ ?_ hb, ?_⟩
  · intro f hf
    show LinearMap.funLeft R C ψ _ ∈ AA.carrier
    rw [hp]
    exact hf
  · rw [hp, ← huw, add_sub_cancel_left, sq_eq_mul]
    exact hw

end Gen

section Scalars

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
variable {X N : Type} [AddCommGroup X] [AddCommGroup N] [Module F X] [Module F N]

lemma fstable_map (M : Submodule R (N → C)) (hM : FStable F M) (ι : X →ₗ[F] N) :
    FStable F (M.map (LinearMap.funLeft R C ι)) := by
  rintro a _ ⟨g, hg, rfl⟩
  refine ⟨_, hM a g hg, ?_⟩
  funext x
  show g (a • ι x) = g (ι (a • x))
  rw [map_smul]

lemma fstable_comap (M : Submodule R (N → C)) (hM : FStable F M) (ψ : N →ₗ[F] X) :
    FStable F (M.comap (LinearMap.funLeft R C ψ)) := by
  intro a g hg
  have := hM a _ hg
  show LinearMap.funLeft R C ψ _ ∈ M
  convert this using 1
  funext x
  show g (a • ψ x) = g (ψ (a • x))
  rw [map_smul]

lemma range_subtype_eq (K : Submodule F N) :
    (K.subtype.toAddMonoidHom).range = (K.mkQ.toAddMonoidHom).ker := by
  ext x
  simp [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]

end Scalars

theorem subquo : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable F AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable F AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ N _ _ _ _ AA hAA K _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨AK, hAK⟩ := exists_res hv AA K.subtype.toAddMonoidHom Subtype.val_injective
    exact ⟨AK, hAK, hAK ▸ fstable_map _ hAA K.subtype⟩
  · obtain ⟨AQ, hAQ⟩ := exists_quo hv AA K.mkQ.toAddMonoidHom K.mkQ_surjective
    exact ⟨AQ, hAQ, hAQ ▸ fstable_comap _ hAA K.mkQ⟩
  · exact invFun_eq _ K.mkQ.toAddMonoidHom K.mkQ_surjective _ (fun x => by simp)
  · intro c cQ cK hc hQ hK
    exact colen_ses hv AA K.subtype.toAddMonoidHom Subtype.val_injective K.mkQ.toAddMonoidHom
      K.mkQ_surjective (range_subtype_eq K) c cQ cK hc hQ hK

end PositivityTheory.HtPt.Rc
end
end

