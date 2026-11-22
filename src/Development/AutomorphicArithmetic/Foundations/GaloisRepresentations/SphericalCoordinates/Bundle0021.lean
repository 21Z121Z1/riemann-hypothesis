import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0875
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.POneAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem congOne_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ}
    (hd : N ∣ N') {g : G.GAf} (h : L.CongOne N' g) : L.CongOne N g := by
  obtain ⟨k, rfl⟩ := hd
  intro v hv
  obtain ⟨w, hw, hv'⟩ := h v hv
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [hv', smul_smul]⟩

private theorem coordA_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.oneAt_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.OneAt := by
  intro hk li p _ D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hF B PD D' t hcls j a hpl hco hloc P x e hU
  obtain ⟨h3, hcop, h3', hcop', hdvd, -⟩ := hlev
  have lev1 : LevOk L N N' 1 := ⟨h3, hcop, h3', hcop', hdvd, fun u hu => by
    have hm : u ∈ L.KN N := ⟨congOne_of_dvd L hdvd hu.1, congOne_of_dvd L hdvd hu.2⟩
    simpa using hm⟩
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hPinc, he'', -, hj'', hpl'', hco'', hloc''⟩ :=
    hk p D G L gb N N' 1 lev1 X X' c₁ hX hL hX' hL' ρ hF D' t P x e hU B j a.1 (PD.lat a.2) hpl hco hloc
  have hco₁ : IsCoordA L (trivX B) N D'' t'' j'' a.1 := by simpa using hco''
  have hpos : 0 < N := by omega
  obtain ⟨w, hmk, hw⟩ := (li p D G L B PD N hpos hcop D' t D'' t'' j j'' a a N' N t t'' hcls hcls'' hpl hpl''
    (coordA_of_dvd L hdvd hco) hco₁ hloc hloc'' 1).1 ⟨by simp, by simp⟩
  have hw1 : ∀ u, j (w u) = j'' u := fun u => by
    rw [hw u]
    simp [actY]
  have hinc : ∀ u, w (inc u) = u := fun u => hpl.1 (by rw [hw1, hj''])
  have hP : ∀ u'', P (w u'') = P'' u'' := fun u'' => by
    have e1 : inc (w u'') = u'' := w.injective (hinc _)
    rw [← hPinc, e1]
  refine ⟨_, GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam X.univ hX hL) N D'' D' t'' t P'' P
    (x ≫ c₁.q) e'' w (LinearEquiv.refl ℂ _) hpos hU'' hmk (fun u => hP u) hU.2.1, fun z => ?_⟩
  simpa using he'' z
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem add_expand {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A) (w : V) :
    f w = ∑ i, ((b.repr w i : ℚ) : ℝ) • f (b i) := by
  conv_lhs => rw [← b.sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := map_ratCast_smul f ℚ ℝ (b.repr w i) (b i)
  simpa using h

private theorem span_basis {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A)
    (hs : Submodule.span ℝ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun i => f (b i))) := by
  rw [← hs]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  rw [add_expand b f w]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem equiv_of_spans {V A B : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A] [AddCommGroup B] [Module ℝ B]
    [FiniteDimensional ℝ B] (th : V →+ A) (Q : V →+ B)
    (hA : Submodule.span ℝ (Set.range th) = ⊤) (hB : Submodule.span ℝ (Set.range Q) = ⊤)
    (dA : Module.finrank ℝ A = Module.finrank ℚ V) (dB : Module.finrank ℝ B = Module.finrank ℚ V) :
    ∃ R : A ≃ₗ[ℝ] B, ∀ w, Q w = R (th w) := by
  let b := Module.finBasis ℚ V
  let bA : Module.Basis (Fin (Module.finrank ℚ V)) ℝ A :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => th (b i)) (span_basis b th hA) (by simp [dA])
  let bB : Module.Basis (Fin (Module.finrank ℚ V)) ℝ B :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => Q (b i)) (span_basis b Q hB) (by simp [dB])
  refine ⟨bA.equiv bB (Equiv.refl _), fun w => ?_⟩
  rw [add_expand b th w, add_expand b Q w, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  have h1 : bA i = th (b i) := by simp [bA]
  have h2 : bB i = Q (b i) := by simp [bB]
  rw [← h1, ← h2, Module.Basis.equiv_apply]
  rfl

theorem UpperTheory.Gal.W2.perExt_of :
    UpperTheory.Gal.W2.PerExt := by
  intro p _ D G L A β ρ Q hQ
  haveI : Module.Finite ℤ D.La := D.finLa
  haveI : Module.Finite ℚ (VQ D) := Module.Finite.base_change ℤ ℚ D.La
  refine equiv_of_spans A.th Q A.span hQ.2.1 A.dim ?_
  rw [← A.dim, A.dimg]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceT
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_not_real {tr nm : ℤ} {r : ℂ} (hd : tr ^ 2 - 4 * nm < 0)
    (hr : r ^ 2 - (tr : ℂ) * r + (nm : ℂ) = 0) : (starRingEnd ℂ) r ≠ r := by
  intro hc
  have him : r.im = 0 := Complex.conj_eq_iff_im.mp hc
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, r = (x : ℂ) := ⟨r.re, by apply Complex.ext <;> simp [him]⟩
  have h1 : x ^ 2 - (tr : ℝ) * x + (nm : ℝ) = 0 := by exact_mod_cast hr
  have h2 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (2 * x - (tr : ℝ))]

theorem UpperTheory.Gal.W2.placeT_of :
    UpperTheory.Gal.W2.PlaceT := by
  intro p _ D G L ha v hv t₀ ht
  have i₀ : Fin D.a := ⟨0, by omega⟩
  have hsub : ∀ i j : Fin D.a, i = j := fun i j => by
    apply Fin.ext; have := i.2; have := j.2; omega
  have hρ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  have hne : (starRingEnd ℂ) D.ρc ≠ D.ρc := rho_not_real D.disc_neg D.ρc_root
  obtain ⟨i, hi⟩ := (L.sig v).1 hv
  have hφ : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = t₀ x := fun x => by
    rw [← ht i]; exact L.s_C i x
  refine ⟨fun v' hv' => ?_, hρ, hne, ?_⟩
  · obtain ⟨j, hj⟩ := (L.sig v').1 hv'
    rw [hi, hj, hsub i j]
  · have hemb := InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i))
    rw [← hi] at hemb
    rcases hemb with h | h
    · left
      have hx : ∀ x, v.embedding (L.e x) = t₀ x := fun x => by rw [h]; exact hφ x
      refine ⟨?_, hx⟩
      unfold sgnV
      rw [if_pos (by rw [hx, hρ])]
    · right
      have hx : ∀ x, v.embedding (L.e x) = (starRingEnd ℂ) (t₀ x) := fun x => by
        rw [h, ComplexEmbedding.conjugate_coe_eq, hφ]
      have hω : v.embedding (L.e (D.ω : D.F)) ≠ D.ρc := by rw [hx, hρ]; exact hne
      refine ⟨?_, fun hall => hω (by rw [hall, hρ]), fun x => by rw [hx, Complex.conj_conj]⟩
      unfold sgnV
      rw [if_neg hω]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowCorr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powCorr_of :
    UpperTheory.Gal.W2.PwOver → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PowCorr := by
  intro hPw hPt p _ D G L gb N N' h X X' c₁ c₂ ρ D' S hact ga hcomp k α
  have w₁ := hPw p D G L gb N N' 1 X X' c₁ k
  have w₂ := hPw p D G L gb N N' h X X' c₂ k
  refine ⟨?_, ?_⟩
  · intro P P'' hP hP'' hga z
    obtain ⟨hu, hex⟩ := hcomp P P'' hP hP'' hga
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    have f'' := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P'' hP''
    apply KS.PowPB.pow_left_hom_ext
    · simp only [Category.assoc, (w₂.2.2.2 α).1, w₁.1]
      simp only [← Category.assoc, f.1, f''.1]
      exact hu
    · intro i
      simp only [Category.assoc, (w₂.2.2.2 α).2 i, w₁.2.1 i]
      simp only [← Category.assoc, f.2.1, f''.2.1]
      rw [hex, Category.assoc, ← w₁.2.2.1, ← Category.assoc, ← hact P'' hP'']
      rfl
  · intro P hP hinj z z' heq
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    refine (f.2.2.2.1 z z').2 (fun j => hinj (z j) (z' j) ?_)
    have e := congrArg (· ≫ Over.Hom.left (KS.pr X.univ.A j)) heq
    simp only [Category.assoc, w₁.2.1 j] at e
    simpa only [← Category.assoc, f.2.1] using e
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowSm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powSm_of :
    UpperTheory.Gal.W2.PowSm := by
  intro X s d g hs hqc hsep A _ _ hA hg k
  have hP : IsProper (KS.pow A k).hom := KS.Leray.isProper_pow_hom A hA.proper k
  have hsm := FibPow.smoothOfRelativeDimension_fibrePower ℂ X s d g hs A hA hg k
  refine ⟨hsm, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · haveI : Smooth ((KS.pow A k).hom ≫ s) := hsm.smooth
    infer_instance
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPwOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i' => ?_) i hf
    · intro hf0
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hf0 _ (Fin.succ_ne_zero j)
    · intro hfs
      rw [hfs 0 (Fin.succ_ne_zero i').symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i' (fun j hj => hfs _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  unfold GlobalTheory.KS.matEnd GlobalTheory.KS.pr
  rw [Pi.lift_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Matrix.diagonal_apply_ne' d hj, GlobalTheory.KS.Model.act_zero, Hom.one_def]

theorem UpperTheory.Gal.W2.pwOver_of :
    UpperTheory.Gal.W2.PwOver := by
  intro p _ D G L gb N N' h X X' c k
  have hpw : c.pw k ≫ (KS.pow X.univ.A k).hom = (KS.pow X'.univ.A k).hom ≫ c.q := by
    delta Leg.pw
    exact KS.Model.powMap_over _ _ _ k
  have hpr : ∀ i : Fin k,
      c.pw k ≫ Over.Hom.left (KS.pr X.univ.A i) = Over.Hom.left (KS.pr X'.univ.A i) ≫ c.tot := by
    intro i
    delta Leg.pw
    exact KS.Model.powMap_pr _ _ _ k i
  refine ⟨hpw, hpr, ?_, fun α => ⟨?_, fun i => ?_⟩⟩
  · intro b
    delta Leg.tot
    have h1 := congrArg Over.Hom.left (c.tr.2.1 b)
    simp only [Over.comp_left] at h1
    rw [← Category.assoc, h1, Category.assoc, c.φ.act b, Category.assoc]
  · delta Leg.tw
    rw [Category.assoc, Over.w, hpw]
  · have hm := congrArg Over.Hom.left
      (matEnd_diagonal_pr X.univ.act (fun s => (algebraMap (𝓞 D.F) D.O (α s) : D.toG.O)) i)
    rw [Over.comp_left, Over.comp_left] at hm
    delta Leg.tw
    refine (Category.assoc _ _ _).trans ((congrArg (c.pw k ≫ ·) hm).trans ?_)
    rw [← Category.assoc, hpr, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSheetOf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU
open scoped Matrix

namespace UpperTheory.Gal.W2

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

private theorem refl_marked {Λ : Type} (N : ℕ) (D : PLat O bar) (t : Λ → D.La) :
    IsMarkedIsom N D D t t (LinearEquiv.refl O D.La) :=
  ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩

private theorem commutes_rho {D : PLat O bar} {P P' : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ρ P) (hP' : IsPeriod D ρ P') (w : D.La ≃ₗ[O] D.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hw : ∀ x, P' (w x) = h (P x)) (a : O) (z : Fin g → ℂ) :
    h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by
    rw [hP.2.2.2.1]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    rw [← hP.1, ← hw, ← hw, map_smul, hP'.1]
  | zero => simp
  | add x y _ _ hx hy => simp only [Matrix.mulVec_add, map_add, hx, hy]
  | smul c x _ hx =>
    have e : ∀ v : Fin g → ℂ, h (c • v) = c • h v := fun v =>
      (h.toLinearMap.restrictScalars ℝ).map_smul c v
    rw [Matrix.mulVec_smul, e, e, hx, Matrix.mulVec_smul]

theorem sheetOf_of : SheetOf := by
  intro O _ bar g ρ Λ F N Cl U i hN hfull
  have hN0 : 0 < N := by omega
  have key : ∀ (P P' : (U.Di i).La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsPeriod (U.Di i) ρ P' → (∀ x, P' x = h (P x)) →
      ∀ (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
        (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P y e →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P' y' e' →
      ∀ z, (e' (h z)).left = (e z).left := by
    intro P P' h hP' hx y y' e e' hy a b z
    subst hy
    have h2 := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.Di i) (U.t i) (U.t i) P P' y e
      (LinearEquiv.refl O _) h hN0 a (refl_marked N _ _) (fun x => hx x) hP'
    have h3 := congrFun (GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.t i) P' y _ _ hN hfull h2 b) (h z)
    simp only [LinearEquiv.symm_apply_apply] at h3
    rw [← h3]
  refine ⟨{ u := U.u i, ex := U.ex i, ov := fun P hP => (U.unif i P hP).1,
            exp := fun P hP => (U.unif i P hP).2.2.1, ker := fun P hP => (U.unif i P hP).2.2.2.1,
            lin := ?_, hol := U.hol i, lift := ?_ }, fun _ => rfl, fun _ _ => rfl⟩
  · intro P P' h hP hP' hx z
    have e : U.u i P = U.u i P' :=
      (U.fibre i P P' hP hP').2 ⟨LinearEquiv.refl O _, h, refl_marked N _ _, fun x => hx x⟩
    exact key P P' h hP' hx _ _ _ _ e (U.unif i P hP) (U.unif i P' hP') z
  · intro m B y hB hy hhol b₀ hb₀ P₀ hP₀ hyb
    obtain ⟨B', i', P, hB', hb', hsub, hP, hu⟩ := U.lift m B y hB hy hhol b₀ hb₀
    have hPb := hP.1 b₀ hb'
    obtain rfl : i' = i := U.disj i' i (P b₀) P₀ hPb hP₀ ((hu b₀ hb').trans hyb)
    obtain ⟨w, h, hw, hwx⟩ := (U.fibre i' (P b₀) P₀ hPb hP₀).1 ((hu b₀ hb').trans hyb)
    have hc := commutes_rho hPb hP₀ w h hwx
    let P' : (Fin _ → ℂ) → ((U.Di i').La →+ (Fin g → ℂ)) := fun b =>
      (h.toLinearMap.toAddMonoidHom.comp (P b)).comp w.symm.toLinearMap.toAddMonoidHom
    have ev : ∀ b x, P' b x = h (P b (w.symm x)) := fun _ _ => rfl
    have hper : ∀ b ∈ B', IsPeriod (U.Di i') ρ (P' b) := fun b hb =>
      isPeriod_comp_isometry_symm _ _ w hw.1 _
        (GlobalTheory.T.comp_linearEquiv_intertwining O bar _ g ρ ρ (P b) h (hP.1 b hb) hc)
    refine ⟨B', P', hB', hb', hsub, ⟨hper, fun x => ?_⟩, ?_, fun b hb => ?_⟩
    · exact (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable.comp_differentiableOn
        (hP.2 (w.symm x))
    · ext1 x
      rw [ev, ← hwx, LinearEquiv.apply_symm_apply]
    · rw [← hu b hb]
      exact ((U.fibre i' (P b) (P' b) (hP.1 b hb) (hper b hb)).2
        ⟨w, h, hw, fun x => by rw [ev, LinearEquiv.symm_apply_apply]⟩).symm

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTateWit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem tateWit_of : TateWit := by
  intro p _ D gb N S s o hX hL ρ D' t P x e hN hNp hU I hI
  classical
  obtain ⟨-, hper, hexp, hker, hact, hweil, heta⟩ := hU
  have hadd : ∀ z w, e (z + w) = e z * e w := hexp.1
  have hsurj : Function.Surjective e := hexp.2.1
  have hlin : ∀ (c : D.O) u, P (c • u) = ρ c *ᵥ P u := hper.1
  have hinj : Function.Injective P := hper.2.1
  haveI : Module.Free ℤ D.toG.La := D.freeLa
  have hlift : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ φ : D.La →+ D'.La, ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (φ a)) :=
    fun n hn hnp => unifCls_lift e P hadd hsurj hker (I.ev n) (I.add n) hn
      (fun y => (I.onto n hn _).2 ⟨y, rfl⟩)
  have hroot : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ v : ℤ, IsCoprime v n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (v : ℂ) / n) :=
    fun n hn hnp => unifCls_root hn _ (I.ζ_prim n hn)
  let f : ℕ → D.La →+ D'.La := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hlift n hn.1 hn.2) else 0
  let nu : ℕ → ℤ := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hroot n hn.1 hn.2) else 0
  have hf : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a)) := by
    intro n hn hnp a
    simp only [f, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hlift n hn hnp) a
  have hnu : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p), IsCoprime (nu n) n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) := by
    intro n hn hnp
    simp only [nu, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hroot n hn hnp)
  have heq : ∀ {n : ℕ}, 0 < n → ∀ v v' : D'.La,
      e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P v') ↔ ∃ w, v = v' + n • w :=
    fun hn v v' => unifCls_eq_iff e P hadd hker hinj hn v v'
  refine ⟨f, nu, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n m hn hm hnm
    have hnp : n.Coprime p := (Nat.coprime_mul_iff_left.1 hnm).1
    refine ⟨?_, fun a => ?_⟩
    · have hz := I.ζ_pow n m hn hm
      have hz' := congrArg (fun u : ℂˣ => (u : ℂ)) hz
      simp only [Units.val_pow_eq_pow_val] at hz'
      rw [(hnu _ (Nat.mul_pos hn hm) hnm).2, (hnu n hn hnp).2, ← Complex.exp_nat_mul] at hz'
      have : (m : ℂ) * (-(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / ((n * m : ℕ) : ℂ)) =
          -(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / n := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        push_cast; field_simp
      rw [this] at hz'
      exact (unifCls_exp_eq_iff hn _ _).1 hz'
    · have ht := I.tower n m hn hm a
      have e1 := hf _ (Nat.mul_pos hn hm) hnm a
      have e2 := hf n hn hnp a
      rw [e1, e2] at ht
      erw [unifCls_tower e P hadd hn hm] at ht
      exact (heq hn _ _).1 ht
  · intro n hn hnp
    refine ⟨(hnu n hn hnp).1, fun c a => ?_, fun a => ?_, fun a' => ?_, fun a a' => ?_⟩
    · have hl := I.lin n c a
      erw [hf n hn hnp (c • a), hf n hn hnp a] at hl
      have h3 := hact c ((n : ℂ)⁻¹ • P (f n a))
      rw [Matrix.mulVec_smul] at h3
      have h4 := hlin c (f n a)
      have h5 : e ((n : ℂ)⁻¹ • P (c • f n a)) = e ((n : ℂ)⁻¹ • P (f n a)) ≫ o.act.act c := by
        rw [h4]; exact h3
      exact (heq hn _ _).1 (hl.trans h5.symm)
    · have h1 := I.ker n hn a
      erw [hf n hn hnp a, unifCls_unit_iff e P hker hinj hn] at h1
      exact h1
    · obtain ⟨y, hy⟩ := (I.onto n hn (e ((n : ℂ)⁻¹ • P a'))).1 (unifCls_pow e P hadd hker hn a')
      rw [hf n hn hnp y] at hy
      obtain ⟨w, hw⟩ := (heq hn _ _).1 hy.symm
      exact ⟨y, w, hw⟩
    · have hiso := I.isom n hn a a'
      rw [hf n hn hnp a, hf n hn hnp a'] at hiso
      have hw := hweil n (f n a) (f n a')
        (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF (f n a) (f n a') : ℂ) / n)) (Complex.exp_ne_zero _))
        hn rfl
      have hu := GlobalTheory.T.weilPairing_complex_value_unique S o.A D.g o.ab hX _ hL x n _ _ _ _ hiso hw
      have hu' := congrArg (fun u : ℂˣ => (u : ℂ)) hu
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hu'
      rw [(hnu n hn hnp).2, ← Complex.exp_int_mul] at hu'
      have : ((2 * D.toG.EF a a' : ℤ) : ℂ) * (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) =
          -(2 * Real.pi * Complex.I) * ((nu n * (2 * D.toG.EF a a') : ℤ) : ℂ) / n := by
        push_cast; ring
      rw [this] at hu'
      exact (unifCls_exp_eq_iff hn _ _).1 hu'.symm
  · intro a
    have h3 : I.ev N a = e ((N : ℂ)⁻¹ • P (t a)) := (hI a).symm.trans (heta a)
    rw [hf N hN hNp a] at h3
    obtain ⟨w, hw⟩ := (heq hN _ _).1 h3
    exact ⟨w, hw⟩
  · intro n hn hnp a
    exact hf n hn hnp a

end UpperTheory.Gal.W2
end
end

