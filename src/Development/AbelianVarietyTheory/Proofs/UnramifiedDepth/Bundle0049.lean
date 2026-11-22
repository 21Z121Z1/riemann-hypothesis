import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartNsmulAndKilledByPPow
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

section
variable {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {d : ℕ} (F : FGLaw R d)

private theorem kill_cc : ∀ (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0
  | 0, j => by simp [mulF]
  | N + 1, j => by
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulF F.F N, pt R d 0] : Fin 2 → Pt R 1 d) q.1 q.2) = 0 := by
      rintro ⟨x, l⟩
      fin_cases x
      · exact kill_cc N l
      · simp [pt]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h) h (F.const j)

private theorem kill_X {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (pt R d i j) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (h3 (i, j))

private theorem kill_zero {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (map_zero ψ)

private theorem kill_one {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) :
    ∀ i j, IsNilpotent ((![a] : Fin 1 → Fin d → S) i j) := fun i j => by
  fin_cases i; exact ha j

private theorem kill_two {a b : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i j, IsNilpotent ((![a, b] : Fin 2 → Fin d → S) i j) := fun i j => by
  fin_cases i
  · exact ha j
  · exact hb j

private theorem kill_add {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (x y : Pt R n d)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0)
    (f : PS R 2 d) : nv s (ev ![x, y] f) a = nv s f ![fun l => nv s (x l) a, fun l => nv s (y l) a] := by
  have := (nv_calculus R S s n d a ha).2.2.1 2 d ![x, y] f (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j)
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem kill_succ {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (N : ℕ) (j : Fin d) :
    nv s (mulF F.F (N + 1) j) ![a] = nv s (F.F j) ![fun l => nv s (mulF F.F N l) ![a], a] := by
  refine (kill_add s ![a] (kill_one ha) _ _ (kill_cc F N) (fun l => by simp [pt]) (F.F j)).trans ?_
  congr 3
  funext l
  exact kill_X s ![a] (kill_one ha) 0 l

private theorem kill_unitL {c : Fin d → S} (hc : ∀ i, IsNilpotent (c i)) (j : Fin d) :
    nv s (F.F j) ![0, c] = c j := by
  have h := kill_add s ![c] (kill_one hc) 0 (pt R d 0) (fun l => by simp) (fun l => by simp [pt]) (F.F j)
  rw [F.unit j] at h
  have h1 : (fun l => nv s ((0 : Pt R 1 d) l) ![c]) = 0 := funext fun l => kill_zero s _ (kill_one hc)
  have h2 : (fun l => nv s (pt R d (0 : Fin 1) l) ![c]) = c := funext fun l => kill_X s _ (kill_one hc) 0 l
  rw [h1, h2] at h
  exact h.symm.trans (kill_X s _ (kill_one hc) 0 j)

private theorem kill_unitR {b : Fin d → S} (hb : ∀ i, IsNilpotent (b i)) (j : Fin d) :
    nv s (F.F j) ![b, 0] = b j := by
  have h0 := kill_two hb (fun _ => IsNilpotent.zero : ∀ i, IsNilpotent ((0 : Fin d → S) i))
  have h := kill_add s ![b, 0] h0 (pt R d 1) (pt R d 0) (fun l => by simp [pt]) (fun l => by simp [pt]) (F.F j)
  rw [F.comm j] at h
  have h1 : (fun l => nv s (pt R d (1 : Fin 2) l) ![b, 0]) = 0 := funext fun l => kill_X s _ h0 1 l
  have h2 : (fun l => nv s (pt R d (0 : Fin 2) l) ![b, 0]) = b := funext fun l => kill_X s _ h0 0 l
  rw [h1, h2] at h
  exact h.trans (kill_unitL s F hb j)

private theorem kill_sq (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {b c : Fin d → S}
    (hb : ∀ i, b i ∈ K) (hc : ∀ i, c i ∈ K) (j : Fin d) : nv s (F.F j) ![b, c] = b j + c j := by
  have hn : ∀ x ∈ K, IsNilpotent x := fun x hx => ⟨2, by rw [pow_two]; exact hK x hx x hx⟩
  have key : ∀ b c : Fin d → S, (∀ i, b i ∈ K) → (∀ i, c i ∈ K) → nv s (F.F j) ![b, c] =
      ∑ l, s (MvPowerSeries.coeff (Finsupp.single (0, l) 1) (F.F j)) * b l +
        ∑ l, s (MvPowerSeries.coeff (Finsupp.single (1, l) 1) (F.F j)) * c l := by
    intro b c hb hc
    have hm : ∀ i l, (![b, c] : Fin 2 → Fin d → S) i l ∈ K := fun i l => by
      fin_cases i
      · exact hb l
      · exact hc l
    rw [(nv_calculus R S s 2 d ![b, c] (fun i l => hn _ (hm i l))).2.2.2.2.2
      (fun _ _ _ _ => hK _ (hm _ _) _ (hm _ _)), F.const j, map_zero, zero_add, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    rfl
  have h1 := key b 0 hb (fun _ => K.zero_mem)
  have h2 := key 0 c (fun _ => K.zero_mem) hc
  rw [kill_unitR s F (fun i => hn _ (hb i))] at h1
  rw [kill_unitL s F (fun i => hn _ (hc i))] at h2
  rw [key b c hb hc, h1, h2]
  simp

private theorem kill_sqN (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {c : Fin d → S}
    (hc : ∀ i, c i ∈ K) (N : ℕ) : ∀ j, nv s (mulF F.F N j) ![c] = (N : S) * c j := by
  have hn : ∀ i, IsNilpotent (c i) := fun i => ⟨2, by rw [pow_two]; exact hK _ (hc i) _ (hc i)⟩
  induction N with
  | zero => intro j; exact (kill_zero s ![c] (kill_one hn)).trans (by simp)
  | succ N ih =>
    intro j
    rw [kill_succ s F hn, funext ih, kill_sq s F K hK (fun i => K.mul_mem_left _ (hc i)) hc]
    push_cast
    ring

private theorem kill_lin (K : Ideal S) {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i))
    (hc : ∀ i, c i ∈ K) (N : ℕ) (j : Fin d) : nv s (mulF F.F N j) ![c] - (N : S) * c j ∈ K * K := by
  let t := Ideal.Quotient.mk (K * K)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_mul, map_natCast]
  refine ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.2.2.2.1 _ t _).trans ?_
  have h : (fun i l => t ((![c] : Fin 1 → Fin d → S) i l)) = ![fun l => t (c l)] := by
    funext i; fin_cases i; rfl
  rw [h]
  refine kill_sqN (t.comp s) F (K.map t) ?_ (fun i => Ideal.mem_map_of_mem t (hc i)) N j
  intro x hx y hy
  obtain ⟨x, hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hx
  obtain ⟨y, hy', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hy
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_mul hx' hy')

private theorem kill_nil {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i)) (N : ℕ) (j : Fin d) :
    IsNilpotent (nv s (mulF F.F N j) ![c]) :=
  ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.1 _ (kill_cc F N j)).1

end

theorem bxChart_nsmul_and_killed : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ) (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), IsNilpotent (p : (R : Type)) → (∀ i, IsNilpotent (a i)) → (∀ N : ℕ, N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a])) ∧ ∃ n : ℕ, p ^ (n + 1) • Y R s a = 0 := by
  intro R₀ _ B O g F Y hY p R s a hp ha
  have h1 : ∀ a : Fin g → (R : Type), (∀ i, IsNilpotent (a i)) → ∀ N : ℕ,
      N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a]) := by
    intro a ha N
    induction N with
    | zero =>
      rw [zero_nsmul, ← hY.zero R s]
      congr 1
      funext j
      exact (kill_zero _ ![a] (kill_one ha)).symm
    | succ N ih =>
      rw [succ_nsmul, ih, hY.law R s _ _ (kill_nil _ F ha N) ha]
      congr 1
      funext j
      exact (kill_succ _ F ha N j).symm
  refine ⟨h1 a ha, ?_⟩
  let J : Ideal (R : Type) := Ideal.span (insert (p : (R : Type)) (Set.range a))
  have hpJ : (p : (R : Type)) ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have h2 : ∀ k : ℕ, ∃ b : Fin g → (R : Type), (∀ i, IsNilpotent (b i)) ∧ (∀ i, b i ∈ J ^ (k + 1)) ∧
      p ^ k • Y R s a = Y R s b := by
    intro k
    induction k with
    | zero =>
      refine ⟨a, ha, fun i => ?_, by simp⟩
      rw [zero_add, pow_one]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    | succ k ih =>
      obtain ⟨b, hb, hbJ, e⟩ := ih
      refine ⟨_, kill_nil _ F hb p, fun i => ?_, by rw [pow_succ', mul_smul, e, h1 b hb p]⟩
      have h3 := kill_lin s.1.toRingHom F (J ^ (k + 1)) hb hbJ p i
      rw [← pow_add] at h3
      have h4 : (p : (R : Type)) * b i ∈ J ^ (k + 1 + 1) := by
        rw [pow_succ' J (k + 1)]
        exact Ideal.mul_mem_mul hpJ (hbJ i)
      simpa using add_mem (Ideal.pow_le_pow_right (by omega : k + 1 + 1 ≤ k + 1 + (k + 1)) h3) h4
  have hfg : J.FG := Submodule.fg_span ((Set.finite_range a).insert _)
  have hle : J ≤ nilradical (R : Type) := by
    refine Ideal.span_le.2 ?_
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hp
    · exact ha i
  obtain ⟨n, hn⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  obtain ⟨b, -, hbJ, e⟩ := h2 (n + 1)
  refine ⟨n, ?_⟩
  rw [e, ← hY.zero R s]
  congr 1
  funext i
  have := Ideal.pow_le_pow_right (by omega : n ≤ n + 1 + 1) (hbJ i)
  rw [hn] at this
  simpa using this

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChart
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G' G f φ) {Z : Scheme.{0}}
    (t' : Z ⟶ S') (t : Z ⟶ S) (ht : t' ≫ f = t) :
    ∃ P : (Over.mk t' ⟶ G') →* (Over.mk t ⟶ G), (∀ x, (P x).left = x.left ≫ φ) ∧ Function.Bijective P := by
  subst ht
  let p : (Over.mk t' ⟶ G') → (Over.mk (t' ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      have := Over.w x
      simp only [Over.mk_hom] at this ⊢
      rw [Category.assoc, h.1.w, ← Category.assoc, this])
  refine ⟨MonoidHom.mk' p fun x y => Over.OverMorphism.ext (h.2 (Over.mk t') x y (p x) (p y) rfl rfl).symm,
    fun _ => rfl, fun x y hxy => ?_, fun z => ?_⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · exact (Over.w x).trans (Over.w y).symm
  · refine ⟨Over.homMk (h.1.lift z.left t' (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _

private theorem spec_comp {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) :
    Spec.map (CommRingCat.ofHom s.1.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type))) =
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (R : Type))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact s.1.comp_algebraMap

theorem bxChart_of_nilChart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  intro R₀ _ G _ _ B e hb hm hn O G' _ _ φ hφ g F X hX
  have h0 : ∀ R, e R 0 = 1 := fun R => by
    have := hm R 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  choose P hP hPb using fun (R : LAlg R₀) (s : LHom O R) => exists_push hφ _ _ (spec_comp s)
  let X' : ∀ R : LAlg R₀, ∀ s : LHom O R, (Fin g → (R : Type)) →
      (Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G') := fun R s a =>
    @X R _ s.1.toRingHom.toAlgebra a
  choose Y hY using fun (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)) => (hb R).2 (P R s (X' R s a))
  have hYl : ∀ R s a, (e R (Y R s a)).left = (X' R s a).left ≫ φ := fun R s a => by rw [hY, hP]
  refine ⟨Y, ⟨fun R s => ?_, fun R R' s f a ha => ?_, fun R s a b ha hb' hab => ?_,
    fun R S s π σ hπσ hσ hπ x hx => ?_, fun R s a b ha hb' => ?_⟩, fun f α A hr hA R s a ha => ?_⟩
  · apply (hb R).1
    rw [hY, h0]
    letI := s.1.toRingHom.toAlgebra
    have : X' R s 0 = 1 := hX.zero R
    rw [this, map_one]
  · apply (hb R').1
    apply Over.OverMorphism.ext
    rw [hn, Over.comp_left, hYl, hYl]
    letI := s.1.toRingHom.toAlgebra
    letI := (f.comp s).1.toRingHom.toAlgebra
    let f' : (R : Type) →ₐ[(O : Type)] (R' : Type) := ⟨f.1.toRingHom, fun _ => rfl⟩
    have := congrArg (fun z => z.left ≫ φ) (hX.nat R R' f' a ha)
    exact (Category.assoc _ _ _).symm.trans this
  · letI := s.1.toRingHom.toAlgebra
    refine hX.inj R a b ha hb' ((hPb R s).1 ?_)
    exact (hY R s a).symm.trans ((congrArg (e R) hab).trans (hY R s b))
  · obtain ⟨z, hz⟩ := (hPb R s).2 (e R x)
    letI := s.1.toRingHom.toAlgebra
    letI := (π.comp s).1.toRingHom.toAlgebra
    let ρ : (R : Type) →ₐ[(O : Type)] (S : Type) := ⟨π.1.toRingHom, fun _ => rfl⟩
    let σ' : (S : Type) →ₐ[(O : Type)] (R : Type) :=
      ⟨σ.1.toRingHom, fun r => congrArg (fun u : LHom O R => u.1 r) hσ⟩
    have h1 : ρ.comp σ' = AlgHom.id _ _ := AlgHom.ext fun r => congrArg (fun u : LHom S S => u.1 r) hπσ
    have h2 : IsNilpotent (RingHom.ker ρ) := ⟨2, hπ.2⟩
    have h3 : spMap ρ ≫ z = 1 := by
      apply (hPb S (π.comp s)).1
      refine Eq.trans ?_ (map_one (P S (π.comp s))).symm
      rw [← h0, ← hx, hn, ← hz]
      apply Over.OverMorphism.ext
      rw [hP, Over.comp_left, Over.comp_left, hP]
      exact Category.assoc _ _ _
    obtain ⟨a, ha, hza⟩ := hX.surj R S ρ σ' h1 h2 z h3
    refine ⟨a, ha, (hb R).1 ?_⟩
    rw [hY, ← hz, hza]
  · apply (hb R).1
    letI := s.1.toRingHom.toAlgebra
    rw [hm, hY, hY, hY, ← map_mul]
    exact congrArg (P R s) (hX.law R a b ha hb')
  · apply (hb R).1
    apply Over.OverMorphism.ext
    letI := s.1.toRingHom.toAlgebra
    rw [← hA s (Y R s a) (X' R s a) (hYl R s a).symm, hYl]
    exact congrArg (fun z => z.left ≫ φ) (hr.2 R a ha)

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdmissibleRowsValueEqRowGaugeStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleRows_value_eq_rowGauge : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  first | exact @GlobalTheory.RowVal.valOf_eq_hRow | exact GlobalTheory.RowVal.valOf_eq_hRow | (intros; apply GlobalTheory.RowVal.valOf_eq_hRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0Statement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_derivationPolynomial_eq_jetAt0 : ∀ (C : Type) [Field C] (dd n : ℕ) (F : Fin dd → PS C 2 dd) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (W : Type) [Fintype W] (E : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (E s) = 0) → ∀ (co : ι → W → C) (P : MvPolynomial ι C), (∀ ℓ ∈ P.vars, ∀ G : PS C n dd, MvPowerSeries.subst E (DofN F (cp ℓ) (uv ℓ) G) = ∑ w, co ℓ w • MvPowerSeries.pderiv C w (MvPowerSeries.subst E G)) → ∀ G : PS C n dd, MvPowerSeries.constantCoeff (DpolyN F cp uv P G) = jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ w, MvPolynomial.C (co ℓ w) * MvPolynomial.X w) P : MvPolynomial W C) (MvPowerSeries.subst E G) := by
  first | exact @GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 | exact GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 | (intros; apply GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiagonalSplit
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal.MapSumDiagonal

theorem map_sum_of_pred {R Q α : Type} [AddCommMonoid R] [AddCommMonoid Q] (P : R → Prop) (f : R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (f0 : f 0 = 0)
    (fadd : ∀ a b, P a → P b → f (a + b) = f a + f b) (s : Finset α) (a : α → R) (ha : ∀ i, P (a i)) :
    P (∑ i ∈ s, a i) ∧ f (∑ i ∈ s, a i) = ∑ i ∈ s, f (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P0, f0]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨Padd _ _ (ha i) ih.1, by rw [fadd _ _ (ha i) ih.1, ih.2]⟩

theorem split_abstract {R Q Orb : Type} [Ring R] [AddCommGroup Q] [Fintype Orb] (P : R → Prop) (h : R → R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (Pmul : ∀ a b, P a → P b → P (a * b))
    (h0 : ∀ a, h a 0 = 0 ∧ h 0 a = 0)
    (hl : ∀ a a' b, P a → P a' → P b → h (a + a') b = h a b + h a' b)
    (hr : ∀ a a' b, P a → P a' → P b → h b (a + a') = h b a + h b a')
    (hs : ∀ a b, P a → P b → h b a = h a b)
    (W W' : R) (hW : P W) (hW' : P W') (hadj : ∀ a b, P a → P b → h (W * a) b = h a (W' * b))
    (hWW : W + W' = 1) (π : Orb → Fin 2 → R) (hπ : ∀ o g, P (π o g))
    (horth : ∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → h (π o g) (W * π o' g') = 0) :
    ∑ o, h (π o 0) (π o 1) = h (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) := by
  classical
  have hWπ : ∀ o g, P (W * π o g) := fun o g => Pmul _ _ hW (hπ o g)
  have e1 : (∑ o, ∑ g, π o g) = ∑ p : Orb × Fin 2, π p.1 p.2 := by rw [Fintype.sum_prod_type]
  have hB : P (∑ p : Orb × Fin 2, W * π p.1 p.2) :=
    (map_sum_of_pred P (fun _ => (0 : Q)) P0 Padd rfl (by simp) _ _ (fun p : Orb × Fin 2 => hWπ p.1 p.2)).1
  rw [e1, Finset.mul_sum]
  rw [(map_sum_of_pred P (fun a => h a (∑ p : Orb × Fin 2, W * π p.1 p.2)) P0 Padd (h0 _).2
    (fun a b ha hb => hl a b _ ha hb hB) Finset.univ (fun p : Orb × Fin 2 => π p.1 p.2)
    (fun p => hπ p.1 p.2)).2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  have e2 : ∀ g, h (π o g) (∑ p : Orb × Fin 2, W * π p.1 p.2) = h (π o g) (W * π o (1 - g)) := by
    intro g
    rw [(map_sum_of_pred P (fun a => h (π o g) a) P0 Padd (h0 _).1
      (fun a b ha hb => hr a b _ ha hb (hπ o g)) Finset.univ (fun p : Orb × Fin 2 => W * π p.1 p.2)
      (fun p => hWπ p.1 p.2)).2]
    refine Finset.sum_eq_single (o, 1 - g) ?_ (by simp)
    intro p _ hp
    apply horth
    rintro ⟨h1, h2⟩
    exact hp (Prod.ext h1.symm h2)
  rw [Fin.sum_univ_two, e2, e2, sub_zero, sub_self, ← hs _ _ (hπ o 1) (hWπ o 0),
    hadj _ _ (hπ o 0) (hπ o 1), ← hr _ _ _ (hWπ o 1) (Pmul _ _ hW' (hπ o 1)) (hπ o 0), ← add_mul, hWW, one_mul]

theorem diagonal_split : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : RawChart C d I κ), RLaw X V → ∀ (Orb : Type) [Fintype Orb] (π : Orb → Fin 2 → Matrix κ κ C) (W W' : Matrix κ κ C), (∀ o g, IntEnd X V (π o g)) → IsEnd X V W W' → W + W' = 1 → (∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → hEnd X (π o g) (W * π o' g') ∈ logInt V κ) → (∑ o, hEnd X (π o 0) (π o 1)) - hEnd X (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ := by
  intro C _ _ V d I _ κ _ _ X hR Orb _ π W W' hπ hE hWW horth
  obtain ⟨P0, Padd, Pmul, h0, hadd, hs, hadj⟩ := GlobalTheory.RowVal.EndCalc.end_calc C V d I κ X hR
  let q := QuotientAddGroup.mk' (logInt V κ)
  have hq : ∀ a, q a = 0 ↔ a ∈ logInt V κ := fun a => QuotientAddGroup.eq_zero_iff a
  have key := split_abstract (IntEnd X V) (fun a b => q (hEnd X a b)) P0 Padd Pmul
    (fun a => ⟨by simp only [(h0 a).1, map_zero], by simp only [(h0 a).2, map_zero]⟩)
    (fun a a' b ha ha' hb => by
      have := (hq _).2 (hadd a a' b ha ha' hb).1
      rw [map_sub, map_add, sub_eq_zero] at this
      exact this.symm)
    (fun a a' b ha ha' hb => by
      have := (hq _).2 (hadd a a' b ha ha' hb).2
      rw [map_sub, map_add, sub_eq_zero] at this
      exact this.symm)
    (fun a b ha hb => by
      have := (hq _).2 (hs a b ha hb)
      rwa [map_sub, sub_eq_zero] at this)
    W W' hE.1 hE.2.1
    (fun a b ha hb => by
      have := (hq _).2 (hadj W W' a b hE ha hb)
      rwa [map_sub, sub_eq_zero] at this)
    hWW π hπ (fun o g o' g' hn => (hq _).2 (horth o g o' g' hn))
  rw [← hq, map_sub, map_sum, sub_eq_zero]
  exact key

end GlobalTheory.RowVal.MapSumDiagonal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem existsUnique_lift_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {OE : Type} [CommRing OE] [Module.Finite ℤ OE]
    (τ : OE →+* C) : ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ := by
  have h : ∀ x : OE, ∃ y : O, algebraMap O C y = τ x := fun x => by
    have h1 : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    have h2 : IsIntegral ℤ (τ x) := h1.map τ.toIntAlgHom
    have h3 : IsIntegral O (τ x) := h2.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h3)
  choose f hf using h
  refine ⟨{ toFun := f
            map_one' := hv.hom_inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hv.hom_inj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hv.hom_inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hv.hom_inj (by rw [hf, map_add, map_add, hf, hf]) }, ?_, ?_⟩
  · exact RingHom.ext hf
  · intro g hg
    refine RingHom.ext fun x => hv.hom_inj ?_
    change algebraMap O C (g x) = algebraMap O C (f x)
    rw [hf, ← hg]
    rfl

theorem embeddings_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  refine ⟨existsUnique_lift_integers hv, fun e τ he => ?_, ?_⟩
  · have h : IsIdempotentElem (tauExt τ e) := by
      unfold IsIdempotentElem
      rw [← map_mul, he]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h
  · intro _ τ x
    have h2 : sig p OE x = sigE p OE x := rfl
    refine ⟨?_, h2⟩
    rw [← h2]
    clear h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tauExt, sig]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end GlobalTheory.ChF
end

