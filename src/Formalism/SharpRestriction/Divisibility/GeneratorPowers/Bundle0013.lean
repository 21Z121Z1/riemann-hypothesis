import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupCopies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem glue_units {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  simp only [res] at hr ⊢
  have hc : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨i, hi⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨s, hs, -⟩ : ∃! s : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => ((r i : Γ(X, U i)))) (fun i j => by
      have h1 := congrArg Units.val (hr i j)
      simp only [Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t = (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i))) (fun i j => by
      have h1 := congrArg (fun v => ((v⁻¹ : Γ(X, U i ⊓ U j)ˣ) : Γ(X, U i ⊓ U j))) (hr i j)
      simp only [← map_inv, Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  have hs' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    fun i => hs i
  have ht' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t =
      (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) := fun i => ht i
  have hst : s * t = 1 := by
    apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hc
    intro i
    show (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom (s * t) =
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs' i, ht' i, Units.mul_inv]
  refine ⟨⟨s, t, hst, by rw [mul_comm]; exact hst⟩, fun i => ?_⟩
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mk]
  exact hs' i

theorem exists_ratio_gen {X : Scheme.{0}} {M : LB X} (hcov : ∀ x : X, ∃ i, x ∈ M.U i) {g₁ g₂ : LB.Gen M}
    (h₁ : g₁.IsGen) (h₂ : g₂.IsGen) : ∃ u : Γ(X, ⊤)ˣ, ∀ i, g₁.s i = res (le_top : M.U i ≤ ⊤) u * g₂.s i := by
  unfold LB.Gen.IsGen at h₁ h₂
  obtain ⟨u, hu⟩ := glue_units M.U hcov (fun i => g₁.s i / g₂.s i) (fun i j => by
    rw [map_div, map_div, h₁ i j, h₂ i j, mul_div_mul_left_eq_div])
  exact ⟨u, fun i => by rw [hu i, div_mul_cancel]⟩

theorem unit_eq_one_of_eSec (hGF : GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (u : Γ(A.left, ⊤)ˣ) (h : (eSec A).appTop.hom u.val = 1) : u = 1 := by
  unfold GlobalFnsSt at hGF
  have hsec : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    rw [Over.w]
    rfl
  obtain ⟨s, hs⟩ := (hGF S A hA).2 u.val
  have h2 : (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s = s := by
    rw [hsec]
    simp
  have hs1 : s = 1 := by
    calc s = (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s := h2.symm
      _ = (Scheme.Hom.appTop (eSec A)).hom ((Scheme.Hom.appTop A.hom).hom s) := rfl
      _ = 1 := by rw [hs, h]
  ext
  rw [← hs, hs1, map_one]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

theorem one_left {S : Scheme.{0}} {X : Over S} {G : Over S} [MonObj G] :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := rfl

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

abbrev fV : Sp T.Fr ⟶ Sp T.V := spMap (algebraMap T.V T.Fr)

abbrev jc (n m : ℕ) : Jet T.V (Fin n × Fin d) m →+* Jet T.Fr (Fin n × Fin d) m :=
  jetCoef (algebraMap T.V T.Fr) (Fin n × Fin d) m

theorem xL_w (m : ℕ) : (spMap (jc (d := d) 1 m) ≫ (xT m).left) ≫ I.G.G.hom =
    spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) ≫ spMap (algebraMap T.V T.Fr) := by
  rw [Category.assoc, Over.w]
  simp only [spMap_comp']
  simp only [jOG, Over.mk_hom, Category.comp_id, spMap_comp']
  congr 1
  ext r
  simp only [jc, jetCoef, RingHom.comp_apply]
  erw [Ideal.Quotient.lift_mk]
  simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  rfl

def xL (m : ℕ) : Sp (Jet T.Fr (Fin 1 × Fin d) m) ⟶ I.t'.G.left :=
  I.m2.cart.1.lift (spMap (jc (d := d) 1 m) ≫ (xT m).left) (spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)))
    (xL_w I xT m)

theorem xL_fst (m : ℕ) : xL I xT m ≫ I.m2.φ = spMap (jc (d := d) 1 m) ≫ (xT m).left := I.m2.cart.1.lift_fst _ _ _

theorem xL_snd (m : ℕ) : xL I xT m ≫ I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) := I.m2.cart.1.lift_snd _ _ _

def xP (m : ℕ) : jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G :=
  Over.homMk (xL I xT m) (by
    show xL I xT m ≫ I.t'.G.hom = spMap _ ≫ 𝟙 _
    rw [xL_snd, Category.comp_id])

def xU (m : ℕ) : (letI := io.toAlgebra; jO y.1 d m 1) ⟶ Xo.univ.t.G :=
  letI := io.toAlgebra
  Over.homMk (xL I xT m ≫ I.m1.φ) (by
    show (xL I xT m ≫ I.m1.φ) ≫ Xo.univ.t.G.hom = spMap _ ≫ y.1.x
    rw [Category.assoc, I.m1.cart.1.w, ← Category.assoc, xL_snd])

theorem ext2 {Z : Scheme.{0}} {a b : Z ⟶ I.t'.G.left} (h1 : a ≫ I.m2.φ = b ≫ I.m2.φ)
    (h2 : a ≫ I.t'.G.hom = b ≫ I.t'.G.hom) : a = b := I.m2.cart.1.hom_ext h1 h2

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

attribute [local instance] Over.cartesianMonoidalCategory

namespace ExpBijectiveUniformisation

section Help

variable {X Y Z : Scheme.{0}}

lemma wchart_comp_le (L : LB X) (g : Y ⟶ X) (z : Z ⟶ Y) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0) ≤ z ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => g) j := by
  intro y hy
  have h1 : (z ≫ g).base y ∈ L.U (j 0) := Set.mem_iInter.1 hy ⟨⟩
  show z.base y ∈ (⋂ k : Fin 1, g.base ⁻¹' (L.U (j k) : Set X))
  refine Set.mem_iInter.2 fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact h1

def genCast {L L' : LB X} (h : L = L') {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L' φ ε) :=
  h ▸ b

def sumQ {X1 Xn : Type} [AddCommGroup X1] [AddCommGroup Xn] {n : ℕ} (xe : Xn ≃+ (Fin n → X1)) (Q : X1 → ℤ) :
    Xn → ℤ :=
  fun x => ∑ i, Q (xe x i)

end Help

section GermN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def jcN (V F : Type) [CommRing V] [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    Sp (Jet F (Fin n × Fin d) m) ⟶ Sp (Jet V (Fin 1 × Fin d) m) :=
  spMap (((jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) :
      Jet F (Fin 1 × Fin d) m →+* Jet F (Fin n × Fin d) m).comp
    (jetCoef (algebraMap V F) (Fin 1 × Fin d) m))

def jptN {V : Type} [CommRing V] {t : SAB H (Sp V)} {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (F : Type)
    [Field F] [Algebra V F] (n m : ℕ) (i : Fin n) : Sp (Jet F (Fin n × Fin d) m) ⟶ t.G.left :=
  jcN V F d n m i ≫ (xT m).left

def IsGermN {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} (P : PELUnif I t) {d n : ℕ}
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t)
    {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)} [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} (pG : IsPowGrp G' t.G n)
    {U' : Unif I D' A' G'} (PU : UnifPowOf pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] (q : ℕ)
    (σ' : U'.toUnifPre.SecGF F q) (f : PS F n d) : Prop :=
  ∀ m, ∃ (z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left)
    (τ : LB.Gen (LB.LinComb U'.LG.L (K := PUnit.{1}) (fun _ => z ≫ UnifPre.gFK (R := V) (G := G') F)
      (fun _ => (q : ℤ))))
    (b : LB.Gen (LB.LinComb P.U.LG.L (K := Fin n)
      (fun i => (z ≫ UnifPre.gFK (R := V) (G := G') F) ≫ (pG.pr i).left) (fun _ => (q : ℤ)))),
    z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
    (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
    GeneratorPullback.MapsAt P.U.LG.L U'.LG.L (fun i => (pG.pr i).left) PU.wL (z ≫ UnifPre.gFK (R := V) (G := G') F) q τ b ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (genCast (congrArg RigLB.L P.bundle) _ _ b)
      (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)) ∧
    ∀ j : Fin 1 → U'.LG.L.ι,
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map
          (homOfLE (wchart_comp_le U'.LG.L (UnifPre.gFK (R := V) (G := G') F) z j)).op).hom
        ((z.app _).hom (σ'.f j)) =
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map (homOfLE le_top).op).hom (toΓ _ (psJet m f)) *
        (τ.s (fun _ => j 0)).val

end GermN

section St

open IsLocalRing

def BidegreeTwoJetStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (q D : ℕ), 4 * D + 4 ≤ q → (D : ℝ) * M0 < q →
  ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f →
    ∃ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q) (g : PS F n (chD C.ch)) (lam : F),
      NuGe D' (sumQ pD.xe Q) F v q s 0 ∧ U'.toUnifPre.ExpandsG F q σ' s ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g ∧
      lam ≠ 0 ∧ (∃ ρ : ℚ, v lam = (ρ : WithTop ℚ) ∧ (ρ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / q) ∧
      ∀ e : Fin n × Fin (chD C.ch) →₀ ℕ, e.degree ≤ D →
        MvPowerSeries.coeff e g = MvPowerSeries.coeff e (lam • MvPowerSeries.map (algebraMap T.Fr F) f)

def GermOfFamSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ q : ℕ, 1 ≤ q →
    (∀ σ' : U'.toUnifPre.SecGF F q, ∃ g : PS F n (chD C.ch),
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g) ∧
    ∀ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q), U'.toUnifPre.ExpandsG F q σ' s →
      NuGe D' (sumQ pD.xe Q) F v q s 0 → ∀ g : PS F n (chD C.ch),
        IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g →
        ∀ e, 0 ≤ v (MvPowerSeries.coeff e g)

end St

end ExpBijectiveUniformisation

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FoldPermutation
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

variable {k : Type} [CommRing k] {d : ℕ}

def embP {n' n : ℕ} (e : Fin n' → Fin n) : Fin n' → Pt k n d := fun b => pt k d (e b)

theorem cz_embP {n' n : ℕ} (e : Fin n' → Fin n) : LogPf.CZ (embP (k := k) (d := d) e) := by
  intro j i
  simp [embP, pt]

theorem cz_ptz {n : ℕ} (b : Fin n) : LogPf.CZ (![pt k d b, 0] : Fin 2 → Pt k n d) := by
  intro j i
  fin_cases j <;> simp [pt]

theorem cc_ev {m n : ℕ} {a : Fin m → Pt k n d} (ha : LogPf.CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have e1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [e1]
  rw [LogPf.ev_add ha, LogPf.ev_C ha, map_add, LogPf.constantCoeff_ev ha h0, add_zero, constantCoeff_C]

theorem pderiv_embP {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (g : PS k n' d) (b : Fin n')
    (j : Fin d) : pderiv k (e b, j) (ev (embP e) g) = ev (embP e) (pderiv k (b, j) g) := by
  classical
  rw [LogPf.pderiv_ev (cz_embP e), Finset.sum_eq_single (b, j)]
  · simp [embP, LogPf.pderiv_pt]
  · intro p _ hp
    rw [show embP (k := k) (d := d) e p.1 p.2 = pt k d (e p.1) p.2 from rfl, LogPf.pderiv_pt, if_neg, mul_zero]
    intro hc
    apply hp
    have h1 : e p.1 = e b := congrArg Prod.fst hc
    have h2 : p.2 = j := congrArg Prod.snd hc
    exact Prod.ext (he h1) h2
  · simp

theorem pderiv_ev_embP_of_notMem_range {n' n : ℕ} (e : Fin n' → Fin n) (g : PS k n' d) (c : Fin n) (hc : ∀ b, e b ≠ c)
    (j : Fin d) : pderiv k (c, j) (ev (embP e) g) = 0 := by
  classical
  refine LogPf.pderiv_ev_zero (cz_embP e) g (c, j) fun b i => ?_
  rw [show embP (k := k) (d := d) e b i = pt k d (e b) i from rfl, LogPf.pderiv_pt, if_neg]
  intro h
  exact hc b (congrArg Prod.fst h)

theorem ev_ptz {n' n : ℕ} (e : Fin n' → Fin n) (b : Fin n') (X : PS k 2 d) :
    ev ![pt k d (e b), 0] X = ev (embP e) (ev ![pt k d b, 0] X) := by
  rw [LogPf.ev_ev (cz_embP e) (cz_ptz b)]
  congr 1
  funext q i
  fin_cases q
  · simp [LogPf.ev_X (cz_embP e), embP, pt]
  · simp [LogPf.ev_zero' (cz_embP e)]

theorem dofN_embP (F : Fin d → PS k 2 d) {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (b : Fin n')
    (u : Fin d → k) (g : PS k n' d) : DofN F (e b) u (ev (embP e) g) = ev (embP e) (DofN F b u g) := by
  unfold DofN
  rw [LogPf.ev_sum (cz_embP e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_sum (cz_embP e), pderiv_embP e he]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_C (cz_embP e), ev_ptz]

section Comm

def cB (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) : Fin n × Fin d → PS k n d := fun t =>
  if t.1 = b then ev (embP (fun _ : Fin 1 => b)) (WickVanishing.Nab.co G u ((0 : Fin 1), t.2)) else 0

theorem inj1 {n : ℕ} (b : Fin n) : Function.Injective (fun _ : Fin 1 => b) := by
  intro x y _
  exact Subsingleton.elim x y

theorem dofN_vf (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN G.F b u g = WickVanishing.Nab.vf (cB G b u) g := by
  classical
  unfold DofN WickVanishing.Nab.vf cB
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos rfl]
    congr 1
    unfold WickVanishing.Nab.co
    rw [LogPf.ev_sum (cz_embP _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LogPf.ev_mul (cz_embP _), LogPf.ev_C (cz_embP _)]
    congr 1
    exact ev_ptz (fun _ : Fin 1 => b) 0 _
  · intro c _ hc
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hc, zero_mul]
  · simp

theorem cB_one (G : FGLaw k d) (u : Fin d → k) : cB G (0 : Fin 1) u = WickVanishing.Nab.co G u := by
  funext t
  have h1 : t.1 = 0 := Subsingleton.elim _ _
  have hp : (embP (k := k) (d := d) (fun _ : Fin 1 => (0 : Fin 1))) = fun j => pt k (n := 1) d j := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  simp only [cB, if_pos h1, hp, LogPf.ev_pt]
  rw [show t = ((0 : Fin 1), t.2) from Prod.ext h1 rfl]

theorem dofN_cB_ne (G : FGLaw k d) {n : ℕ} (b c : Fin n) (hbc : b ≠ c) (u v : Fin d → k) (t : Fin n × Fin d) :
    DofN G.F b u (cB G c v t) = 0 := by
  unfold cB
  split_ifs
  · unfold DofN
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_ev_embP_of_notMem_range _ _ b (fun _ => Ne.symm hbc) j, mul_zero]
  · unfold DofN
    simp

theorem dofN_comm (G : FGLaw k d) {n : ℕ} (b b' : Fin n) (u v : Fin d → k) (g : PS k n d) :
    DofN G.F b u (DofN G.F b' v g) = DofN G.F b' v (DofN G.F b u g) := by
  classical
  rw [dofN_vf G b, dofN_vf G b', dofN_vf G b', dofN_vf G b, ← sub_eq_zero, WickVanishing.Nab.vf_comm]
  have hz : (fun t => WickVanishing.Nab.vf (cB G b u) (cB G b' v t) - WickVanishing.Nab.vf (cB G b' v) (cB G b u t)) =
      fun _ => (0 : PS k n d) := by
    funext t
    rw [← dofN_vf G b, ← dofN_vf G b']
    by_cases hb : b = b'
    · rw [← hb]
      have hE : ∀ (w : Fin d → k) (X : PS k 1 d),
          DofN G.F b w (ev (embP (fun _ : Fin 1 => b)) X) = ev (embP (fun _ : Fin 1 => b)) (DofN G.F 0 w X) :=
        fun w X => dofN_embP G.F (fun _ : Fin 1 => b) (inj1 b) 0 w X
      unfold cB
      by_cases ht : t.1 = b
      · rw [if_pos ht, if_pos ht, hE, hE, ← LogPf.ev_sub (cz_embP _), dofN_vf G (0 : Fin 1),
          dofN_vf G (0 : Fin 1), cB_one, cB_one, WickVanishing.Nab.co_bracket G u v, LogPf.ev_zero' (cz_embP _)]
      · rw [if_neg ht, if_neg ht]
        unfold DofN
        simp
    · rw [dofN_cB_ne G b b' hb, dofN_cB_ne G b' b (Ne.symm hb), sub_zero]
  rw [hz, WickVanishing.Nab.vf_zeroc]

end Comm

section Fold

variable {n' n : ℕ} (F : Fin d → PS k 2 d)
  (hF : ∀ (b b' : Fin n) (v v' : Fin d → k) (G : PS k n d), DofN F b v (DofN F b' v' G) = DofN F b' v' (DofN F b v G))
  (e : Fin n' → Fin n) (he : Function.Injective e) {ι ι' : Type} [Fintype ι] [Fintype ι']
  (cp : ι → Fin n) (u : ι → Fin d → k) (cp' : ι' → Fin n') (u' : ι' → Fin d → k) (φ : ι' → ι)
  (hφ : Function.Injective φ) (hcp : ∀ l, cp (φ l) = e (cp' l)) (hu : ∀ l, u (φ l) = u' l)
include hF he hφ hcp hu

end Fold

section Val

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (K : Type) [CommRing K]
  [Algebra ℚ K] [Algebra R K]

end Val

end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
end
end

