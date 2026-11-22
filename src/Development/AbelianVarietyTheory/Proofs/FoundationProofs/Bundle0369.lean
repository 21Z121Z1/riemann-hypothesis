import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0368
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairingStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_dual_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), f ≠ 0 → (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∃ π, IsAutRepU π ∧ ∃ f' : S →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ v, f' v ∈ π) ∧ (∀ (x : infU E n) v, f' (ρ x v) = RU E n x (f' v)) ∧ ∀ (κ : Type) (R : Finset κ) (s : κ → UA E n) (c : ℂ), (∀ i ∈ R, s i ∈ finU E n) → (∀ v, ∑ i ∈ R, RU E n (s i) (f v) = c • f v) → ∀ v, ∑ i ∈ R, RU E n (s i) (f' v) = c • f' v := by
  first | exact @GlobalTheory.FrameAut.VecProj.exists_autRep_projection | exact GlobalTheory.FrameAut.VecProj.exists_autRep_projection | (intros; apply GlobalTheory.FrameAut.VecProj.exists_autRep_projection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactificationOpenOfClosed
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.FlatRow

theorem isOpen_closure_of_isOpen_components {Z : Type} [TopologicalSpace Z]
    (h : ∀ z : Z, IsOpen (irreducibleComponent z)) {W : Set Z} (hW : IsOpen W) : IsOpen (closure W) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨irreducibleComponent z, ?_, h z, mem_irreducibleComponent⟩
  have hne : (irreducibleComponent z ∩ W).Nonempty := mem_closure_iff.1 hz _ (h z) mem_irreducibleComponent
  intro y hy
  refine mem_closure_iff.2 fun O hO hyO => ?_
  obtain ⟨a, -, ha⟩ := isIrreducible_irreducibleComponent.isPreirreducible O W hO hW ⟨y, hy, hyO⟩ hne
  exact ⟨a, ha⟩

theorem isOpen_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens), IsClosed (U : Set (Xo.XF c)) → IsOpen (FramedFlatCoordinates.compactification Y U) := by
  intro E _ _ _ H Dw l Xo c Y U _
  have i₀ : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  have i₁ : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := inferInstance
  have hn : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := fun x => by
    let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian (FramedFlatCoordinates.genFibre Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (RingHom.id c.F)))
  have := Y.jQ_open
  exact isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)

end GlobalTheory.FlatRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisBaseChangeLocalAlgebra
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisLocal

open EigenSplit LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD)

theorem eigenBasis_map {O R R' I : Type} [CommRing O] [CommRing R] [CommRing R'] [Finite I]
    {σ : I → O →+* R} (hσ : IsSplitting σ) {n m : ℕ} (ρ : O →+* Module.End R (Fin n → R)) (f : R →+* R')
    (ρ' : O →+* Module.End R' (Fin n → R')) (hf : ∀ a x, f ∘ ρ a x = ρ' a (f ∘ x)) (τ : I)
    (b : Fin m → Fin n → R) (hb : ∀ i, b i ∈ eigenSub ρ (σ τ))
    (H : ∀ c ∈ eigenSub ρ (σ τ), ∃! d : Fin m → R, ∑ i, d i • b i = c) :
    (∀ i, f ∘ b i ∈ eigenSub ρ' (f.comp (σ τ))) ∧
      ∀ c ∈ eigenSub ρ' (f.comp (σ τ)), ∃! d : Fin m → R', ∑ i, d i • (f ∘ b i) = c := by
  let _ := f.toAlgebra
  let F : (Fin n → R) →ₗ[R] (Fin n → R') := (Algebra.linearMap R R').compLeft (Fin n)
  have hF : IsBaseChange R' F := IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R R')
  have hf' : ∀ a x, F (ρ a x) = ρ' a (F x) := hf
  have hB := isBaseChange_eigenMapAlgebra hσ hf' hF τ
  let b' : Fin m → eigenSub ρ (σ τ) := fun i => ⟨b i, hb i⟩
  have key : ∀ c : eigenSub ρ (σ τ), ∃! d, Fintype.linearCombination R b' d = c := fun c => by
    refine (existsUnique_congr fun d => ?_).1 (H _ c.2)
    rw [Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rfl
  let B : Module.Basis (Fin m) R (eigenSub ρ (σ τ)) :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ ((Function.bijective_iff_existsUnique _).2 key)).symm
  have hBi : ∀ i, (B i : Fin n → R) = b i := fun i => by
    simp [B, b', Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply_single]
  let B' := hB.basis B
  have hB' : ∀ i, (B' i : Fin n → R') = f ∘ b i := fun i => by
    rw [← hBi, IsBaseChange.basis_apply]
    rfl
  refine ⟨fun i => hB' i ▸ (B' i).2, fun c hc => ?_⟩
  have k : ∀ d : Fin m → R', ∑ i, d i • (f ∘ b i) = c ↔ B'.equivFun ⟨c, hc⟩ = d := fun d => by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff, eq_comm]
    simp [hB']
  simp only [k]
  exact existsUnique_eq'

theorem isEigBasis_iff {O R : Type} [CommRing O] [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {n m : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e) {act : OAct O G}
    {ρ : O →+* Module.End R (Fin n → R)} (hρ : ∀ a c, prodPts (ρ a c) e = prodPts c e ≫ act.act a)
    (χ : O →+* R) (b : Fin m → Fin n → R) :
    EigenvectorLieDegree.IsEigBasis act χ (fun i => prodPts (b i) e) ↔ (∀ i, b i ∈ eigenSub ρ χ) ∧
      ∀ c ∈ eigenSub ρ χ, ∃! d : Fin m → R, ∑ i, d i • b i = c := by
  have mem : ∀ c, EigenvectorLieDegree.IsEigVec act χ (prodPts c e) ↔ c ∈ eigenSub ρ χ := fun c => by
    rw [mem_eigenSub]
    refine (and_iff_right (isTangent_prodPts he.1 c)).trans (forall_congr' fun a => ?_)
    rw [← hρ, ← (prodPts_injective he).eq_iff]
    rw [prodPts_smul, Over.OverMorphism.ext_iff]
    rfl
  have cb : ∀ d c, IsLieComb d (fun i => prodPts (b i) e) (prodPts c e) ↔ ∑ i, d i • b i = c := fun d c => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    rw [prodPts_prodPts he.1, eq_comm]
    exact (prodPts_injective he).eq_iff
  refine and_congr (forall_congr' fun i => mem _) ⟨fun h c hc => ?_, fun h w hw => ?_⟩
  · exact (existsUnique_congr fun d => cb d c).1 (h _ ((mem c).2 hc))
  · obtain ⟨c, rfl⟩ := exists_prodPts he hw.1
    exact (existsUnique_congr fun d => cb d c).2 (h _ ((mem c).1 hw))

theorem isEigBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  intro E _ _ _ H l c R R' _ _ _ j g t t' n τ m v v' hv hv'
  let σ₀ : (E →+* ℂ) → 𝓞 E →+* c.F := fun τ =>
    (τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E)
  have hσ₀ : Function.Injective σ₀ := fun τ τ' h =>
    (isSplitting_complex E).injective
      (RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a))
  have hσ : IsSplitting fun τ => j.comp (σ₀ τ) :=
    isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) j (by
      simpa using (isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  obtain ⟨e', he', ee⟩ := exists_isLieBasis_baseChange R R' g _ _ _ n.cart t.semi.smooth N e he
  obtain ⟨ρ, hρ⟩ := exists_action he t.act
  obtain ⟨ρ', hρ'⟩ := exists_action he' t'.act
  choose b hb using fun i => exists_prodPts he (hv.1 i).1
  obtain rfl : v = fun i => prodPts (b i) e := (funext hb).symm
  obtain rfl : v' = fun i => prodPts (g ∘ b i) e' := funext fun i =>
    Over.OverMorphism.ext (n.cart.1.hom_ext ((hv' i).trans (prodPts_left n.cart ee _).symm)
      ((Over.w _).trans (Over.w _).symm))
  obtain ⟨h1, h2⟩ := (isEigBasis_iff he hρ _ b).1 hv
  exact (isEigBasis_iff he' hρ' _ _).2
    (eigenBasis_map hσ ρ g ρ' (action_baseChange n.cart he' ee n.act hρ hρ') τ b h1 h2)

end GlobalTheory.EigBasisLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisLocalizationAtPrime
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisPrime

theorem eig_localization {R R' O L L' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (S : Submonoid R)
    [IsLocalization S R'] [CommRing O] [Module.Finite ℤ O] [AddCommGroup L] [Module R L] [Module O L]
    [SMulCommClass O R L] [AddCommGroup L'] [Module R' L'] [Module O L'] [SMulCommClass O R' L'] (f : L →+ L')
    (hs : ∀ (r : R) x, f (r • x) = algebraMap R R' r • f x) (ha : ∀ (a : O) x, f (a • x) = a • f x)
    (lift : ∀ y, ∃ q ∈ S, ∃ x, f x = algebraMap R R' q • y) (uniq : ∀ x, f x = 0 → ∃ q ∈ S, q • x = 0)
    (χ : O →+* R) {m : ℕ} (v : Fin m → L)
    (hv : ∀ w : L, (∀ a, a • w = χ a • w) → ∃! c : Fin m → R, w = ∑ i, c i • v i)
    (w : L') (hw : ∀ a, a • w = algebraMap R R' (χ a) • w) : ∃! c : Fin m → R', w = ∑ i, c i • f (v i) := by
  classical
  have unit : ∀ q ∈ S, IsUnit (algebraMap R R' q) := fun q hq => IsLocalization.map_units R' ⟨q, hq⟩
  have inj : ∀ d : Fin m → R', ∑ i, d i • f (v i) = 0 → d = 0 := fun d hd => by
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples_of_finite S d
    choose d' hd' using hqi
    have h0 : f (∑ i, d' i • v i) = 0 := by
      simp only [map_sum, hs, hd', Algebra.smul_def, mul_smul]
      rw [← Finset.smul_sum, hd, smul_zero]
    obtain ⟨r, hr, h1⟩ := uniq _ h0
    have h2 : r • d' = 0 := (hv 0 (by simp)).unique
      (by rw [← h1, Finset.smul_sum]; simp [mul_smul]) (by simp)
    funext i
    have h3 := congrArg (algebraMap R R') (congrFun h2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hd', Algebra.smul_def, Pi.zero_apply,
      map_zero] at h3
    exact (unit q hq).mul_right_eq_zero.1 ((unit r hr).mul_right_eq_zero.1 h3)
  obtain ⟨q, hq, x, hx⟩ := lift w
  have h1 : ∀ a : O, ∃ r ∈ S, r • (a • x - χ a • x) = 0 := fun a => uniq _ (by
    rw [map_sub, ha, hs, hx, smul_comm a, hw, smul_comm, sub_self])
  choose r hr h1 using h1
  obtain ⟨s, hsp⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  have hQ : ∏ a ∈ s, r a ∈ S := S.prod_mem fun a _ => hr a
  obtain ⟨c, hc, -⟩ := hv ((∏ a ∈ s, r a) • x) fun a => by
    have : a ∈ Submodule.span ℤ (s : Set O) := hsp ▸ Submodule.mem_top
    induction this using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_coe.1 hb)
      rw [smul_comm b, smul_comm (χ b), ← sub_eq_zero, ← smul_sub, hk, _root_.mul_comm, mul_smul, h1, smul_zero]
    | zero => simp
    | add b b' _ _ e e' => rw [add_smul, e, e', map_add, add_smul]
    | smul k b _ e => rw [smul_assoc, e, map_zsmul, smul_assoc]
  have h2 := congrArg f hc
  simp only [map_sum, hs, hx, smul_smul] at h2
  obtain ⟨u, hu⟩ := ((unit _ hQ).mul (unit q hq)).exists_left_inv
  have h3 : w = ∑ i, (u * algebraMap R R' (c i)) • f (v i) := by
    simp only [mul_smul u]
    rw [← Finset.smul_sum, ← h2, smul_smul, hu, one_smul]
  refine ⟨_, h3, fun c' hc' => sub_eq_zero.1 (inj _ ?_)⟩
  simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [← hc', ← h3, sub_self]

theorem isEigBasis_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (t : SAB H (Sp R)) (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act χ v → (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v' := by
  intro E _ _ _ H R _ p _ t t' n χ m v v' hv hv'
  have := t.semi.smooth
  have : ∀ s : R, Smooth (Chart.Gs t.G s).hom := fun s => show Smooth (pullback.snd t.G.hom _) from inferInstance
  let j := algebraMap R (Localization.AtPrime p)
  choose g hg hgu using fun x : epsR R ⟶ t.G => existsUnique_isVecOver (f := j) n.cart.1 x
  let f₀ : Serre.Lie t.act → Serre.Lie t'.act := fun x =>
    Serre.Lie.mk _ (g x.hom) ((hg _).isTangent n.cart x.isTangent)
  have hf : ∀ x y, f₀ x = y ↔ IsVecOver j n.φ x.hom y.hom := fun x y =>
    ⟨fun e => e ▸ hg _, fun e => Serre.Lie.ext (hgu _ _ e).symm⟩
  have comb : ∀ (k : ℕ) (c : Fin k → R) (x : Fin k → Serre.Lie t.act),
      f₀ (∑ i, c i • x i) = ∑ i, j (c i) • f₀ (x i) := fun k c x =>
    (hf _ _).2 ((lieComb_baseChange _ _ j t.G t'.G n.φ n.cart k (fun i => (x i).hom) _ c (fun i => (f₀ (x i)).hom) _
      (fun i => hg _) ((Serre.Lie.isLieComb_iff c x _).2 rfl)).2 ((Serre.Lie.isLieComb_iff _ _ _).2 rfl))
  let f : Serre.Lie t.act →+ Serre.Lie t'.act := AddMonoidHom.mk' f₀ fun x y => by
    simpa using comb 2 1 ![x, y]
  have hs : ∀ (r : R) x, f (r • x) = j r • f x := fun r x => by
    change f₀ _ = _ • f₀ _
    simpa using comb 1 ![r] ![x]
  have ha : ∀ (a : 𝓞 E) x, f (a • x) = a • f x := fun a x => (hf _ _).2 (by
    have := hg x.hom
    simp only [IsVecOver] at this ⊢
    change (g x.hom ≫ t'.act.act a).left ≫ _ = _ ≫ (x.hom ≫ t.act.act a).left
    rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv n.cart (epsR (Localization.AtPrime p))
    (spMap (algebraMap R (DualNumber (Localization.AtPrime p)))) (spMap_comp_spMap _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv n.cart (𝟙_ (Over (Sp (Localization.AtPrime p)))) (spMap j)
    (Category.id_comp _).symm
  have one : (1 : Over.mk (spMap j) ⟶ t.G).left = η[t'.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have lift : ∀ y, ∃ q ∈ p.primeCompl, ∃ x, f x = j q • y := fun y => by
    obtain ⟨q, hq, w, hw, hwy⟩ := Chart.tan_prime_lift p (y' := e y.hom) (Over.OverMorphism.ext (by
      refine Eq.trans ?_ one.symm
      rw [Over.comp_left, he, ← y.isTangent]
      exact (Category.assoc _ _ _).symm))
    refine ⟨q, hq, Serre.Lie.mk _ w ((Chart.isTan_iff _).1 hw), (hf _ _).2 ?_⟩
    have := congrArg (fun z => z.left) hwy
    simp only [Over.comp_left, he] at this
    exact (Category.assoc _ _ _).trans this.symm
  have uniq : ∀ x, f x = 0 → ∃ q ∈ p.primeCompl, q • x = 0 := fun x hx => by
    obtain ⟨q, hq, h⟩ := Chart.tan_prime_uniq p (w := x.hom) ((Chart.isTan_iff _).2 x.isTangent)
      (Over.OverMorphism.ext (by
        rw [← map_one e, he]
        exact ((hf _ _).1 hx).symm))
    exact ⟨q, hq, Serre.Lie.ext h⟩
  let y : Fin m → Serre.Lie t.act := fun i => Serre.Lie.mk _ (v i) (hv.1 i).1
  have hy : v' = fun i => (f (y i)).hom := funext fun i => hgu _ _ (hv' i)
  subst hy
  refine ⟨fun i => ⟨Serre.Lie.isTangent _, Serre.Lie.mem_eig_iff_left.1 fun a => ?_⟩, fun w hw => ?_⟩
  · rw [← ha, (Serre.Lie.mem_eig_iff_left (v := y i)).2 (hv.1 i).2 a, hs]
    rfl
  · refine (existsUnique_congr fun c => ?_).1 (eig_localization p.primeCompl f hs ha lift uniq χ y
      (fun z hz => (existsUnique_congr fun c => ?_).1
        (hv.2 z.hom ⟨z.isTangent, (Serre.Lie.mem_eig_iff_left (τ := χ) (v := z)).1 hz⟩))
      (Serre.Lie.mk _ w hw.1) ((Serre.Lie.mem_eig_iff_left (τ := j.comp χ) (v := Serre.Lie.mk _ w hw.1)).2 hw.2))
    · rw [Serre.Lie.isLieComb_iff]
      exact ⟨fun h => congrArg Serre.Lie.hom h, fun h => Serre.Lie.ext h⟩
    · exact (Serre.Lie.isLieComb_iff c y _).trans ⟨fun h => Serre.Lie.ext h, fun h => congrArg Serre.Lie.hom h⟩

end GlobalTheory.EigBasisPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.FlatRow.EigLocal

open GlobalTheory.Serre

theorem hom_ext_of_loc {R : Type} [CommRing R] {X : Scheme.{0}} {f g : Sp R ⟶ X}
    (h : ∀ (p : Ideal R) [p.IsPrime], spMap (algebraMap R (Localization.AtPrime p)) ≫ f =
      spMap (algebraMap R (Localization.AtPrime p)) ≫ g) : f = g := by
  let q : ∀ p : PrimeSpectrum R, Sp (Localization.AtPrime p.asIdeal) ⟶ Sp R := fun p => spMap (algebraMap R _)
  have : ∀ p, Flat (q p) := fun p => by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ p.asIdeal.primeCompl)
  have : Surjective (Sigma.desc q) := Surjective.sigmaDesc_of_union_range_eq_univ (by
    refine Set.eq_univ_of_forall fun p : PrimeSpectrum R => Set.mem_iUnion.2 ⟨p, IsLocalRing.closedPoint _, ?_⟩
    exact PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)))
  have : Epi (Sigma.desc q) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (Sigma.desc q)]
  refine Sigma.hom_ext _ _ fun p => ?_
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
  exact h p.asIdeal

section Res

variable {R R' O : Type} [CommRing R] [CommRing R'] [CommRing O] {f : R →+* R'} {A : Over (Sp R)} {A' : Over (Sp R')}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem fst_dual (f : R →+* R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (Chart.dualMapR f) =
      spMap f ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem scale_dual (f : R →+* R') (c : R) :
    spMap (epsScaleR (f c)) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem isVecOver_mul (h : IsGrpPullback A' A (spMap f) φ) {v w : epsR R ⟶ A} {v' w' : epsR R' ⟶ A'}
    (hv : IsVecOver f φ v v') (hw : IsVecOver f φ w w') : IsVecOver f φ (v * w) (v' * w') := by
  let k : Over.mk ((epsR R').hom ≫ spMap f) ⟶ epsR R := Over.homMk (spMap (Chart.dualMapR f)) (by
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
  have e := h.2 (epsR R') v' w' (k ≫ v) (k ≫ w) hv.symm hw.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

variable [IsCommMonObj A] [IsCommMonObj A']

theorem exists_res (h : IsGrpPullback A' A (spMap f) φ) (a : OAct O A) (a' : OAct O A')
    (ha : ∀ x, (a'.act x).left ≫ φ = φ ≫ (a.act x).left) :
    ∃ ρ : Lie a →ₛₗ[f] Lie a', (∀ w, IsVecOver f φ w.hom (ρ w).hom) ∧ ∀ (x : O) w, ρ (x • w) = x • ρ w := by
  choose r hr hu using fun w : Lie a => existsUnique_isVecOver h.1 w.hom
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Lie a → Lie a', ∀ w, (ρ w).hom = r w :=
    ⟨fun w => Lie.mk a' (r w) ((hr w).isTangent h w.isTangent), fun _ => rfl⟩
  have key : ∀ (w : Lie a) (w' : Lie a'), IsVecOver f φ w.hom w'.hom → ρ w = w' := fun w w' e =>
    Lie.ext ((hρ w).trans (hu w _ e).symm)
  replace hr : ∀ w, IsVecOver f φ w.hom (ρ w).hom := fun w => hρ w ▸ hr w
  have h₁ : ∀ v w, ρ (v + w) = ρ v + ρ w := fun v w => key _ _ (by
    rw [Lie.hom_add, Lie.hom_add]; exact isVecOver_mul h (hr v) (hr w))
  have h₂ : ∀ (c : R) w, ρ (c • w) = f c • ρ w := fun c w => key _ _ (by
    have e := hr w
    unfold IsVecOver at e ⊢
    rw [Lie.hom_smul_left, Lie.hom_smul_left]
    exact (Category.assoc _ _ _).trans ((congrArg (spMap (epsScaleR (f c)) ≫ ·) e).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ w.hom.left) (scale_dual f c)).trans (Category.assoc _ _ _)))))
  have h₃ : ∀ (x : O) w, ρ (x • w) = x • ρ w := fun x w => key _ _ (by
    have e := hr w
    unfold IsVecOver at e ⊢
    rw [Lie.hom_act_smul, Lie.hom_act_smul, Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, e]
    exact Category.assoc _ _ _)
  exact ⟨⟨⟨ρ, h₁⟩, h₂⟩, hr, h₃⟩

theorem isEigVec_iff (a : OAct O A) (χ : O →+* R) (w : Lie a) :
    EigenvectorLieDegree.IsEigVec a χ w.hom ↔ ∀ x, x • w = χ x • w :=
  ⟨fun h x => Lie.ext (Over.OverMorphism.ext (h.2 x)),
    fun h => ⟨w.isTangent, fun x => congrArg (fun u : Lie a => u.hom.left) (h x)⟩⟩

theorem isEigBasis_iff (a : OAct O A) (χ : O →+* R) {m : ℕ} (v : Fin m → Lie a) :
    EigenvectorLieDegree.IsEigBasis a χ (fun i => (v i).hom) ↔ (∀ i x, x • v i = χ x • v i) ∧
      ∀ w : Lie a, (∀ x, x • w = χ x • w) → ∃! c : Fin m → R, w = ∑ i, c i • v i := by
  refine and_congr (forall_congr' fun i => isEigVec_iff a χ _) ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · exact (existsUnique_congr fun c => (Lie.isLieComb_iff c v _).trans Lie.ext_iff.symm).1
      (h w.hom ((isEigVec_iff a χ w).2 hw))
  · exact (existsUnique_congr fun c => (Lie.isLieComb_iff c v _).trans (Lie.ext_iff (v := Lie.mk a w hw.1)).symm).2
      (h (Lie.mk a w hw.1) ((isEigVec_iff a χ _).1 hw))

end Res

theorem exists_smul_eq_zero {R O : Type} [CommRing R] [CommRing O] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] (a : OAct O A) (p : Ideal R) [p.IsPrime] (w : Lie a)
    (h : spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ w.hom.left =
      spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ (1 : epsR R ⟶ A).left) :
    ∃ q ∉ p, q • w = 0 := by
  have : ∀ s : R, Smooth (Chart.Gs A s).hom := fun s => show Smooth (pullback.snd A.hom _) from inferInstance
  obtain ⟨q, hq, hs⟩ := Chart.tan_prime_uniq (G := A) p (w := w.hom) ((Chart.isTan_iff _).2 w.isTangent) (by
    rw [← MonObj.comp_one (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.AtPrime p))))]
    exact Over.OverMorphism.ext h)
  exact ⟨q, hq, Lie.ext (Over.OverMorphism.ext (congrArg (fun u => u.left) hs))⟩

theorem eq_zero_of_loc {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {w : M}
    (h : ∀ (p : Ideal R) [p.IsPrime], ∃ q ∉ p, q • w = 0) : w = 0 := by
  have : (Submodule.span R {w}).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q, hq, e⟩ := h p
    exact hq (hI ((Submodule.mem_annihilator_span_singleton _ _).2 e))
  have h1 : (1 : R) ∈ (Submodule.span R {w}).annihilator := this ▸ Submodule.mem_top
  exact (one_smul R _).symm.trans ((Submodule.mem_annihilator_span_singleton _ _).1 h1)

theorem eigBasis_of_loc {R O M : Type} [CommRing R] [AddCommGroup M] [Module R M] [SMul O M] (χ : O → R) {m : ℕ}
    (u : Fin m → M)
    (loc : ∀ (p : Ideal R) [p.IsPrime], ∃ (M' : Type) (_ : AddCommGroup M') (_ : Module (Localization.AtPrime p) M')
      (_ : SMul O M') (ρ : M →ₛₗ[algebraMap R (Localization.AtPrime p)] M'),
      (∀ (x : O) w, ρ (x • w) = x • ρ w) ∧ (∀ w, ρ w = 0 → ∃ q ∉ p, q • w = 0) ∧
      (∀ i (x : O), x • ρ (u i) = algebraMap R (Localization.AtPrime p) (χ x) • ρ (u i)) ∧
      ∀ w : M', (∀ x : O, x • w = algebraMap R (Localization.AtPrime p) (χ x) • w) →
        ∃! c : Fin m → Localization.AtPrime p, w = ∑ i, c i • ρ (u i)) :
    (∀ i (x : O), x • u i = χ x • u i) ∧
      ∀ w : M, (∀ x : O, x • w = χ x • w) → ∃! c : Fin m → R, w = ∑ i, c i • u i := by
  refine ⟨fun i x => sub_eq_zero.1 (eq_zero_of_loc (R := R) fun p _ => ?_), fun w hw => ?_⟩
  · obtain ⟨M', _, _, _, ρ, h₁, h₂, h₃, -⟩ := loc p
    exact h₂ _ (by rw [map_sub, h₁, h₃, map_smulₛₗ, sub_self])
  have ex : w ∈ Submodule.span R (Set.range u) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    refine eq_zero_of_loc (R := R) fun p _ => ?_
    obtain ⟨M', _, _, _, ρ, h₁, h₂, -, h₄⟩ := loc p
    obtain ⟨c, hc, -⟩ := h₄ (ρ w) fun x => by rw [← h₁, hw, map_smulₛₗ]
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Finset.univ : Finset (Fin m)) c
    choose b hb using fun i => hqi i (Finset.mem_univ _)
    obtain ⟨r, hr, e⟩ := h₂ (q • w - ∑ i, b i • u i) (by
      rw [map_sub, map_smulₛₗ, hc, map_sum, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smulₛₗ, hb, smul_smul, Algebra.smul_def])
    refine ⟨r * q, p.primeCompl.mul_mem hr hq, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul, sub_eq_zero.1 ((smul_sub _ _ _).symm.trans e)]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ex
  refine ⟨c, hc.symm, fun c' hc' => funext fun i => Chart.eq_of_loc fun p _ => ?_⟩
  obtain ⟨M', _, _, _, ρ, h₁, -, -, h₄⟩ := loc p
  have k : ∀ c : Fin m → R, w = ∑ i, c i • u i →
      ρ w = ∑ i, algebraMap R (Localization.AtPrime p) (c i) • ρ (u i) := fun c e => by
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ _ _ _
  exact congrFun ((h₄ (ρ w) fun x => by rw [← h₁, hw, map_smulₛₗ]).unique (k _ hc') (k _ hc.symm)) i

end GlobalTheory.FlatRow.EigLocal

open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal in

theorem GlobalTheory.FlatRow.isEigBasis_of_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)), (∀ (p : Ideal R) [p.IsPrime], ∃ (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) ∧ EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v') → EigenvectorLieDegree.IsEigBasis t.act χ v := by
  intro E _ _ _ H R _ t χ m v h
  have := t.semi.smooth
  have hT : ∀ i, IsTangent (v i) := fun i => hom_ext_of_loc fun p _ => by
    obtain ⟨t', n, v', hv, hb⟩ := h p
    have e := PolBaseChange.eSec_comm n.cart
    unfold eSec at e
    rw [← e, ← (hb.1 i).1, ← Category.assoc, ← fst_dual, Category.assoc, ← hv i, Category.assoc]
  obtain ⟨u, rfl⟩ : ∃ u : Fin m → Lie t.act, v = fun i => (u i).hom := ⟨fun i => Lie.mk _ _ (hT i), rfl⟩
  refine (isEigBasis_iff t.act χ u).2 (eigBasis_of_loc χ u fun p _ => ?_)
  obtain ⟨t', n, v', hv, hb⟩ := h p
  obtain ⟨ρ, hρ, hx⟩ := exists_res n.cart t.act t'.act n.act
  obtain rfl : v' = fun i => (ρ (u i)).hom :=
    funext fun i => (existsUnique_isVecOver n.cart.1 _).unique (hv i) (hρ _)
  have hb' := (isEigBasis_iff t'.act _ fun i => ρ (u i)).1 hb
  refine ⟨Lie t'.act, inferInstance, inferInstance, inferInstance, ρ, hx, fun w hw => exists_smul_eq_zero _ p w ?_, hb'⟩
  have e := hρ w
  have e₀ := hρ 0
  rw [map_zero, Lie.hom_zero, Lie.hom_zero] at e₀
  rw [hw, Lie.hom_zero] at e
  exact e.symm.trans e₀
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemiabelianActionPullbackWeight
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.IntegralEigFrame

open Matrix

section Lie

variable {R K O : Type} [CommRing R] [CommRing K] [CommRing O]

end Lie

theorem exists_char {E L : Type} [Field E] [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L)) (τ : E →+* L) :
    ∃ χ : 𝓞 E →+* AdelicDegreeTameRamification.valRing L 𝔓,
      (algebraMap (AdelicDegreeTameRamification.valRing L 𝔓) L).comp χ = τ.comp (algebraMap (𝓞 E) E) :=
  ⟨(τ.comp (algebraMap (𝓞 E) E)).codRestrict (AdelicDegreeTameRamification.valRing L 𝔓) fun z =>
    𝔓.valuation_le_one (K := L) (RingOfIntegers.mapRingHom τ z), rfl⟩

end GlobalTheory.IntegralEigFrame
end
end

