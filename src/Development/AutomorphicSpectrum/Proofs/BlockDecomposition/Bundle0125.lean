import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcCoverProof

theorem lcCover : CrystallineSemistableComparison.E.LcCover := by
  intro U ι f
  let O : ι → U.Opens := fun a => ⟨f ⁻¹' {a}, f.isLocallyConstant.isOpen_fiber a⟩
  have hcov : iSup O = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨f x, rfl⟩
  have hval : ∀ (a : ι) (v : (O a).toScheme), f ((O a).ι v) = a := fun a v => v.2
  refine ⟨fun a => (O a).toScheme, fun a => (O a).ι, hval, ?_, ?_, ?_⟩
  · intro V g a hg
    have hr : Set.range g ⊆ Set.range (O a).ι := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg v
    exact ⟨IsOpenImmersion.lift (O a).ι g hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro x y h
    refine U.sheaf.eq_of_locally_eq' O ⊤ (fun a => homOfLE le_top) hcov.ge x y fun a => ?_
    have e : O a ≤ (O a).ι ''ᵁ ⊤ := by simp
    have hm : U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op =
        U.presheaf.map (homOfLE (x := (O a).ι ''ᵁ ⊤) le_top).op ≫ U.presheaf.map (homOfLE e).op := by
      rw [← Functor.map_comp]
      rfl
    have := congrArg (U.presheaf.map (homOfLE e).op).hom (h a)
    change (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom x =
      (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom y
    rw [hm]
    exact this
  · intro R _ G x
    have hG := (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond)
    have hS : Sieve.ofArrows (fun a => (O a).toScheme) (fun a => (O a).ι) ∈ Scheme.etaleTopology U :=
      Scheme.zariskiTopology_le_etaleTopology _
        (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hcov))
    have hsf := hG _ hS
    rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hsf
    refine hsf x ?_
    intro a b Z gi gj h
    by_cases hab : a = b
    · subst hab
      have : gi = gj := by rwa [cancel_mono] at h
      rw [this]
    · have hE : IsEmpty Z := ⟨fun z => hab (by
        have h1 := hval a (gi z)
        have h2 := hval b (gj z)
        rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, h2] at h1
        exact h1.symm)⟩
      have hz := (Sheaf.isTerminalOfBotCover G Z (Scheme.bot_mem_grothendieckTopology Z)).isZero
      have := ModuleCat.subsingleton_of_isZero hz
      exact Subsingleton.elim _ _

end GlobalTheory.CompanionTheory.LcCoverProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechLine

variable {X : Scheme.{0}} (D : LineData X)

theorem u_self {V : Scheme.{0}} (a : V ⟶ D.Y) (h : a ≫ D.f = a ≫ D.f) : D.u a a h = 1 := by
  have h2 : D.u a a h * D.u a a h = D.u a a h * 1 := by
    rw [mul_one]
    exact D.coc a a a h h
  exact mul_left_cancel h2

theorem u_congr {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha
  subst hb
  rfl

def lineFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ D.Y)) (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) :
    ComposableArrows (SingleObj (GL (Fin 1) Γ(V, ⊤))) k where
  obj _ := SingleObj.star _
  map {i j} _ := Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j))
  map_id i := by rw [u_self]; exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp {i j l} _ _ := by
    rw [SingleObj.comp_as_mul]
    refine Eq.trans ?_ (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _)
    rw [mul_comm, D.coc]

variable {D}

theorem exists_pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ y : Fin (k + 1) → (U ⟶ D.Y), ∃ x h, z = cechPt D.f k x y h := by
  obtain ⟨x, y, h, hz⟩ := (hC D.Y X D.f k U).1 z
  exact ⟨y, x, h, hz⟩

def pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) : Fin (k + 1) → (U ⟶ D.Y) :=
  (exists_pts hC z).choose

theorem pts_spec (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ x h, z = cechPt D.f k x (pts hC z) h := by
  exact (exists_pts hC z).choose_spec

theorem pts_eq (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) (i j : Fin (k + 1)) :
    pts hC z i ≫ D.f = pts hC z j ≫ D.f := by
  obtain ⟨x, h, -⟩ := pts_spec hC z
  exact (h i).trans (h j).symm

theorem pts_cechPt (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ D.Y))
    (h : ∀ i, y i ≫ D.f = x) : pts hC (cechPt D.f k x y h) = y := by
  obtain ⟨x', h', hz⟩ := pts_spec hC (cechPt D.f k x y h)
  exact ((hC D.Y X D.f k U).2.1 _ _ _ _ _ _ hz).symm

theorem pts_res (hC : CechPt) {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech D.f) k U) (i : Fin (k + 1)) :
    pts hC (Sx.res g z) i = g ≫ pts hC z i := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.1 V g
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem pts_along (hC : CechPt) {k p : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    pts hC (Sx.along z θ) i = pts hC z (θ.toOrderHom i) := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.2 p θ
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem scalar_map {A B : CommRingCat.{0}} (f : A ⟶ B) (u : (A : Type)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map f.hom.toMonoidHom u) =
      Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

variable (D) in
theorem lineFun_res {U V : Scheme.{0}} {k : ℕ} (g : V ⟶ U) (y : Fin (k + 1) → (U ⟶ D.Y))
    (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) (y' : Fin (k + 1) → (V ⟶ D.Y))
    (hy' : ∀ i j, y' i ≫ D.f = y' j ≫ D.f) (e : ∀ i, y' i = g ≫ y i) :
    lineFun D y' hy' = (show Fin (k + 1) ⥤ (glCat 1).obj Γ(U, ⊤) from lineFun D y hy) ⋙
      ((glCat 1).map (Scheme.Γ.map g.op)).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j _ => ?_)
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y' i) (y' j) (hy' i j)) =
    Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.op).hom
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j)))
  rw [← scalar_map]
  congr 1
  rw [u_congr D (e i) (e j) (hy' i j) (by rw [Category.assoc, Category.assoc, hy i j]),
    D.nat g (y i) (y j) (hy i j)]
  rfl

variable (D) in

def lineMap (hC : CechPt) : cech D.f ⟶ ofCat (glCat 1) where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
      naturality := fun U U' g => by
        ext z
        exact lineFun_res D g.unop _ (pts_eq hC _) _ (pts_eq hC _) (fun i => pts_res hC g.unop _ i) }
  naturality n m θ := by
    ext U z
    change lineFun D (pts hC (Sx.along (show Sx (cech D.f) n.unop.len U.unop from z) θ.unop)) (pts_eq hC _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
    exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1))
      (u_congr D (pts_along hC _ θ.unop i) (pts_along hC _ θ.unop j) _ _)

theorem lineMap_exists : CrystallineSemistableComparison.E.CechPt → CrystallineSemistableComparison.E.LineMap := by
  intro hC X D
  refine ⟨lineMap D hC, ?_⟩
  unfold CrystallineSemistableComparison.E.LineData.IsMap
  intro V x a h
  have hp := pts_cechPt (D := D) hC x a h
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (D.u (pts hC (cechPt D.f 1 x a h) 0) (pts hC (cechPt D.f 1 x a h) 1) (pts_eq hC _ 0 1))) = _
  rw [u_congr D (congrFun hp 0) (congrFun hp 1) _ ((h 0).trans (h 1).symm)]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end GlobalTheory.CompanionTheory.CechLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocSplit
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LocSplitProof

theorem locSplit : CrystallineSemistableComparison.E.LocSplit := by
  intro U hU P hP
  obtain ⟨S, hS, hSP⟩ := hP
  rw [Scheme.etaleTopology, Scheme.mem_grothendieckTopology_iff] at hS
  obtain ⟨𝒰, h𝒰⟩ := hS
  have hsurj : Surjective (Limits.Sigma.desc 𝒰.f) := by
    constructor
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    refine ⟨(Limits.Sigma.ι 𝒰.X i) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc, hy]
  have het : Etale (Limits.Sigma.desc 𝒰.f) := by
    have := 𝒰.sigma.map_prop ⟨⟩
    simpa [Scheme.Cover.sigma_f] using this
  obtain ⟨s, hs⟩ := hU _ (Limits.Sigma.desc 𝒰.f) het hsurj
  have hlc : IsLocallyConstant (fun u : U => ((sigmaMk 𝒰.X).symm (s u)).1) := by
    intro t
    have hfst : IsOpen (Sigma.fst ⁻¹' t : Set (Σ i, 𝒰.X i)) := by
      rw [isOpen_sigma_iff]
      intro i
      by_cases hi : i ∈ t
      · convert isOpen_univ
        ext
        simp [hi]
      · convert isOpen_empty
        ext
        simp [hi]
    exact hfst.preimage ((sigmaMk 𝒰.X).symm.continuous.comp s.continuous)
  refine ⟨𝒰.I₀, ⟨fun u => ((sigmaMk 𝒰.X).symm (s u)).1, hlc⟩, ?_⟩
  intro V g a hg
  have hrange : Set.range (g ≫ s) ⊆ Set.range (Limits.Sigma.ι 𝒰.X a) := by
    rintro _ ⟨v, rfl⟩
    have h1 : ((sigmaMk 𝒰.X).symm (s (g v))).1 = a := hg v
    rcases hq : (sigmaMk 𝒰.X).symm (s (g v)) with ⟨i, y⟩
    rw [hq] at h1
    subst h1
    refine ⟨y, ?_⟩
    have h2 : sigmaMk 𝒰.X ⟨i, y⟩ = s (g v) := by rw [← hq]; simp
    rw [sigmaMk_mk] at h2
    rw [h2, Scheme.Hom.comp_apply]
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Limits.Sigma.ι 𝒰.X a = g ≫ s :=
    ⟨_, IsOpenImmersion.lift_fac (Limits.Sigma.ι 𝒰.X a) (g ≫ s) hrange⟩
  have hgl : g = l ≫ 𝒰.f a := by
    have h3 : l ≫ 𝒰.f a = l ≫ Limits.Sigma.ι 𝒰.X a ≫ Limits.Sigma.desc 𝒰.f := by simp
    rw [h3, ← Category.assoc, hl, Category.assoc, hs, Category.comp_id]
  rw [hgl]
  exact hSP V _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk a)) l)

end GlobalTheory.CompanionTheory.LocSplitProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarMeasureSingleton
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem isStdV_measure_singleton_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  intro F _ _ v lam hstd
  obtain ⟨hH, h1⟩ := hstd
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : CharZero (Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hs : ∀ x : Fv F v, lam {x} = lam {0} := by
    intro x
    rw [← measure_preimage_add lam x ({x} : Set (Fv F v))]
    congr 1
    ext y
    simp
  by_contra h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 ENNReal.one_ne_top
  have hcard : ((Finset.range N).image (fun n : ℕ => (n : Fv F v))).card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsum : lam (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      = N * lam {0} := by
    rw [← sum_measure_singleton, Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, hcard,
      nsmul_eq_mul]
  have hsub : (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact natCast_mem (v.adicCompletionIntegers F) n
  have hle := measure_mono (μ := lam) hsub
  rw [hsum, h1] at hle
  exact absurd hN (not_lt.2 hle)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapNsmulTwGen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CstE.KapRedP

theorem up_smul_eq {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (r : ZMod q) (c : ℕ)
    (h : (c : ZMod q) = r) (m : M) : (ULift.up r : ULift.{1} (ZMod q)) • m = c • m := by
  have e : (ULift.up r : ULift.{1} (ZMod q)) = ((c : ℕ) : ULift.{1} (ZMod q)) := by
    ext; rw [ULift.down_natCast, h]
  rw [e, Nat.cast_smul_eq_nsmul]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := congrArg (fun ψ => ψ.hom x) (φ.hom.naturality g.op)
  exact h.symm

theorem map_nsmul_twGen {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (c : ℕ) :
    Sec.map (resι _ (tw q i)) (c • twGen i ζ) = c • resGen i ζ :=
  map_nsmul _ _ _

theorem kapRed : CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapRed := by
  intro hLc _ hKap hRed Q q _ _ h i U ζ ξ hξ f
  obtain ⟨W, j, hj, -, -, hG⟩ := hLc U (ZMod Q) f
  refine (hG (ZMod q) ((GlobalTheory.EtC.res _ (tw q i)).X 0)
    (fun a => Sec.res (j a) (Sec.map (resι _ _) (kap i ξ (f.map (ZMod.castHom h (ZMod q))))))).unique
    (fun a => ?_) (fun a => rfl)
  have hξ' : (primRes (j a) ξ).1 = (primRes (j a) ζ).1 ^ (Q / q) := by
    change (j a).appTop.hom ξ.1 = ((j a).appTop.hom ζ.1) ^ (Q / q)
    rw [hξ, map_pow]
  have hL : Sec.res (j a) (kap i ζ f) = a.val • twGen i (primRes (j a) ζ) := by
    rw [(hKap Q i U ζ f).1 (W a) (j a) a (hj a)]
    exact up_smul_eq a a.val (ZMod.natCast_zmod_val a) _
  have hR : Sec.res (j a) (kap i ξ (f.map (ZMod.castHom h (ZMod q)))) = a.val • twGen i (primRes (j a) ξ) := by
    rw [(hKap q i U ξ (f.map (ZMod.castHom h (ZMod q)))).1 (W a) (j a) (ZMod.castHom h (ZMod q) a)
      (fun v => by simp [hj a v])]
    exact up_smul_eq _ a.val (by rw [ZMod.castHom_apply, ZMod.natCast_val]) _
  rw [(redMap Q q i).nat (j a) 0, res_map, res_map, hL, hR, map_nsmul_twGen, map_nsmul_twGen, map_nsmul,
    hRed Q q h i (W a) (primRes (j a) ζ) (primRes (j a) ξ) hξ']

end GlobalTheory.CompanionTheory.CstE.KapRedP
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBasicOpenOfIsUnitSub
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.RootPowLC

theorem mem_basicOpen_prod {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤)) (u : U)
    (h : ∀ a ∈ t, u ∈ U.basicOpen (s a)) : u ∈ U.basicOpen (∏ a ∈ t, s a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, U.basicOpen_of_isUnit isUnit_one]
    trivial
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    exact ⟨h a (Finset.mem_insert_self a t), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩

theorem exists_notMem_basicOpen {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤))
    (h : ∏ a ∈ t, s a = 0) (u : U) : ∃ a ∈ t, u ∉ U.basicOpen (s a) := by
  by_contra hc
  push_neg at hc
  have hm := mem_basicOpen_prod t s u hc
  rw [h, Scheme.basicOpen_zero] at hm
  exact hm

theorem mem_basicOpen_of_isUnit_sub {U : Scheme.{0}} (x y : Γ(U, ⊤)) (h : IsUnit (x - y)) (u : U)
    (hx : u ∉ U.basicOpen x) : u ∈ U.basicOpen y := by
  rw [Scheme.mem_basicOpen_top] at hx ⊢
  have h1 : IsUnit (U.presheaf.germ ⊤ u trivial (x - y)) := h.map _
  rw [map_sub, sub_eq_add_neg] at h1
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h2 | h2
  · exact absurd h2 hx
  · simpa using h2.neg

theorem isUnit_appTop_of_mem {V U : Scheme.{0}} (g : V ⟶ U) (x : Γ(U, ⊤))
    (h : ∀ v : V, g v ∈ U.basicOpen x) : IsUnit (g.appTop.hom x) := by
  refine RingedSpace.isUnit_of_isUnit_germ V.toRingedSpace ⊤ _ fun v _ => ?_
  have e : V.basicOpen (g.appTop.hom x) = g ⁻¹ᵁ U.basicOpen x := (Scheme.preimage_basicOpen g x).symm
  have hv : v ∈ V.basicOpen (g.appTop.hom x) := by
    rw [e]
    exact h v
  exact (Scheme.mem_basicOpen_top V (g.appTop.hom x) v).1 hv

theorem exists_isPow (hP : PrimAlg) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤))
    (r : Γ(U, ⊤)) (hr : r ^ q = 1) :
    ∃ f : LocallyConstant U (ZMod q), IsPow ζ f r ∧
      ∀ (u : U) (a : ZMod q), u ∉ U.basicOpen (r - ζ.1 ^ a.val) → f u = a := by
  classical
  have hprod : ∏ a : ZMod q, (r - ζ.1 ^ a.val) = 0 := by
    rw [← (hP q _ ζ).2.2.1 r, hr, sub_self]
  have hex : ∀ u : U, ∃ a : ZMod q, u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ (fun a : ZMod q => r - ζ.1 ^ a.val) hprod u
    exact ⟨a, ha⟩
  have huniq : ∀ (u : U) (a b : ZMod q), a ≠ b → u ∉ U.basicOpen (r - ζ.1 ^ a.val) →
      u ∈ U.basicOpen (r - ζ.1 ^ b.val) := by
    intro u a b hab ha
    apply mem_basicOpen_of_isUnit_sub _ _ _ u ha
    have hd : (r - ζ.1 ^ a.val) - (r - ζ.1 ^ b.val) = ζ.1 ^ b.val - ζ.1 ^ a.val := by ring
    rw [hd]
    exact (hP q _ ζ).2.1 b a (Ne.symm hab)
  obtain ⟨f0, hf0def⟩ : ∃ f0 : U → ZMod q, f0 = fun u => Classical.choose (hex u) := ⟨_, rfl⟩
  have hf0 : ∀ u, u ∉ U.basicOpen (r - ζ.1 ^ (f0 u).val) := by
    intro u
    rw [hf0def]
    exact Classical.choose_spec (hex u)
  have hf0_iff : ∀ u a, f0 u = a ↔ u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u a
    constructor
    · rintro rfl
      exact hf0 u
    · intro ha
      by_contra hne
      exact (hf0 u) (huniq u a (f0 u) (Ne.symm hne) ha)
  have hloc : IsLocallyConstant f0 := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    have hfib : f0 ⁻¹' {a} = ⋂ b ∈ (Finset.univ.erase a : Finset (ZMod q)), (U.basicOpen (r - ζ.1 ^ b.val) : Set U) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ,
        and_true, SetLike.mem_coe]
      rw [hf0_iff]
      constructor
      · intro ha b hb
        exact huniq u a b (Ne.symm hb) ha
      · intro h ha
        obtain ⟨a', ha'⟩ := hex u
        by_cases heq : a' = a
        · exact ha' (heq ▸ ha)
        · exact ha' (h a' heq)
    rw [hfib]
    exact isOpen_biInter_finset fun b _ => (U.basicOpen (r - ζ.1 ^ b.val)).isOpen
  refine ⟨⟨f0, hloc⟩, ?_, fun u a ha => (hf0_iff u a).mpr ha⟩
  delta CrystallineSemistableComparison.E.IsPow
  intro V g a hga
  have hunitb : ∀ b : ZMod q, b ≠ a → IsUnit (g.appTop.hom (r - ζ.1 ^ b.val)) := fun b hb =>
    isUnit_appTop_of_mem g _ (fun v => huniq (g v) a b (Ne.symm hb) ((hf0_iff (g v) a).mp (hga v)))
  have hprodV : ∏ b : ZMod q, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val) = 0 := by
    have h0 := congrArg g.appTop.hom hprod
    rw [map_prod, map_zero] at h0
    simpa only [map_sub, map_pow] using h0
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)] at hprodV
  have hu : IsUnit (∏ b ∈ Finset.univ.erase a, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one (fun b hb => ?_)
    have h1 := hunitb b (Finset.ne_of_mem_erase hb)
    simpa only [map_sub, map_pow] using h1
  have h0 : g.appTop.hom r - g.appTop.hom ζ.1 ^ a.val = 0 := hu.mul_left_eq_zero.mp hprodV
  show g.appTop.hom r = (g.appTop.hom ζ.1) ^ a.val
  exact sub_eq_zero.mp h0

theorem rootPow : CrystallineSemistableComparison.E.PrimAlg → CrystallineSemistableComparison.E.RootPow := by
  intro hP q _ U ζ
  refine ⟨fun r hr => ?_, fun ξ => ?_⟩
  · obtain ⟨f, hf, -⟩ := exists_isPow hP q U ζ r hr
    exact ⟨f, hf⟩
  · have hξq : ξ.1 ^ q = 1 := (hP q _ ξ).1
    obtain ⟨f, hf, hloc⟩ := exists_isPow hP q U ζ ξ.1 hξq
    refine ⟨f, hf, fun u => ?_⟩
    have hprod : ∏ a : ZMod q, (ξ.1 - ζ.1 ^ a.val) = 0 := by
      rw [← (hP q _ ζ).2.2.1 ξ.1, hξq, sub_self]
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ
      (fun a : ZMod q => ξ.1 - ζ.1 ^ a.val) hprod u
    rw [hloc u a ha]
    by_contra hna
    set m := a.val with hm
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have ha' : a = (m : ZMod q) := (ZMod.natCast_zmod_val a).symm
    have hcop : ¬ m.Coprime q := by
      intro hc
      exact hna (ha' ▸ (ZMod.isUnit_iff_coprime m q).2 hc)
    set g := Nat.gcd m q with hgdef
    have hg1 : g ≠ 1 := hcop
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right m hq
    have hgq : g ∣ q := Nat.gcd_dvd_right m q
    have hgm : g ∣ m := Nat.gcd_dvd_left m q
    set k := q / g with hkdef
    have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hklt : k < q := Nat.div_lt_self hq (by omega)
    have hζq : ζ.1 ^ q = 1 := (hP q _ ζ).1
    have hζmk : (ζ.1 ^ m) ^ k = 1 := by
      obtain ⟨m', hm'⟩ := hgm
      have e1 : m * k = q * m' := by
        rw [hm', hkdef, mul_comm g m', mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
      rw [← pow_mul, e1, pow_mul, hζq, one_pow]
    have hunit : IsUnit (ξ.1 ^ k - 1) := by
      have hne : ((k : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        exact absurd (Nat.le_of_dvd hkpos hd) (by omega)
      have hu := (hP q _ ξ).2.1 (k : ZMod q) 0 hne
      rwa [ZMod.val_natCast_of_lt hklt, ZMod.val_zero, pow_zero] at hu
    have hdvd : ξ.1 - ζ.1 ^ m ∣ ξ.1 ^ k - 1 := by
      have hs := sub_dvd_pow_sub_pow ξ.1 (ζ.1 ^ m) k
      rwa [hζmk] at hs
    apply ha
    rw [Scheme.mem_basicOpen_top]
    exact isUnit_of_dvd_unit (map_dvd _ hdvd) (hunit.map _)

end GlobalTheory.CompanionTheory.RootPowLC
end

