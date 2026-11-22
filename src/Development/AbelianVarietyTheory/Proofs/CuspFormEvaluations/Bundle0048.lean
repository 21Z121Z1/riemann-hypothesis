import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0037
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionPolynomialExpressionCoeffFieldExtensioStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectionPolynomialExpression_coeffFieldExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (k : ℤ) (F : Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree ∧ ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support, algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) * ∏ b, nabBC hle nab y k (F b) (colOf m b) = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab (y.res hle h) k (F b) (colOf m b) := by
  first | exact @GlobalTheory.FieldBC.polyNab_fieldBC | exact GlobalTheory.FieldBC.polyNab_fieldBC | (intros; apply GlobalTheory.FieldBC.polyNab_fieldBC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBiextensionChartWithGermsFramedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biextension_chart_with_germs_framed_point : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S), ∃ C : ChartAt Xo c y, FrTruncC y C ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f := by
  first | exact @GlobalTheory.ChartRing.exists_chartAt_with_germs | exact GlobalTheory.ChartRing.exists_chartAt_with_germs | (intros; apply GlobalTheory.ChartRing.exists_chartAt_with_germs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_cover_level_sections : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b) := by
  first | exact @GlobalTheory.exists_faithfullyFlat_isVtOver | exact GlobalTheory.exists_faithfullyFlat_isVtOver | (intros; apply GlobalTheory.exists_faithfullyFlat_isVtOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HodgeWeightDominanceConditionStatement
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_weight_dominance_condition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first | exact @GlobalTheory.FrameRead.cof_image | exact GlobalTheory.FrameRead.cof_image | (intros; apply GlobalTheory.FrameRead.cof_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicEnumerationSurjectiveLocalRing
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IsotropicEnum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem comp_list_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T' ⟶ T) (L : List (T ⟶ G)) :
    h ≫ L.prod = (L.map fun x => h ≫ x).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons x L ih => simp [MonObj.comp_mul, ih]

theorem inZh_comp (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) {T T' : Over Xo.X} (h : T' ⟶ T)
    {a : Fin n → (T ⟶ Xo.univ.t.G)} (ha : InZh Xo Λ N a) : InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have hl : (List.ofFn fun j => (h ≫ a j) ≫ Xo.univ.t.act.act (cm i j)) =
        (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j)).map fun y => h ≫ y := by
      simp [List.map_ofFn, Function.comp_def, Category.assoc]
    rw [hl, ← comp_list_prod, h1, MonObj.comp_one]

theorem ev_sum {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) {m : ℕ} (hm : 0 < m) {n : ℕ} (v : Fin n → Dw.La) :
    I.ev m (∑ j, v j) = (List.ofFn fun j => I.ev m (v j)).prod := by

  have h0 : I.ev m 0 = 1 := by
    have h := I.add m 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Fin.sum_univ_succ, I.add, ih (fun j => v j.succ), List.ofFn_succ, List.prod_cons]

theorem exists_eq_of_isAlgClosed (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hw : ∀ i, InZh Xo Λ N (w i))
    (hinj : Function.Injective w) (a : Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) : ∃ i, w i = a := by
  classical
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x (Spec.preimage (x ≫ Xo.s)).hom
    (by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  have hM : 0 < N ^ 2 := pow_pos hN 2

  have evEq : ∀ u u' : Dw.La, Dw.ModN (N ^ 2) (u - u') → I.ev (N ^ 2) u = I.ev (N ^ 2) u' := by
    intro u u' h
    have h1 : I.ev (N ^ 2) (u - u') = 1 := (I.ker _ hM _).2 h
    have h2 := I.add (N ^ 2) (u - u') u'
    rw [sub_add_cancel, h1, _root_.one_mul] at h2
    exact h2

  have key : ∀ c : Fin n → (ptO Xo x ⟶ Xo.univ.t.G), InZh Xo Λ N c →
      ∃ y : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
        ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
          ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • y j)) ∧ ∀ b, I.ev (N ^ 2) (y b) = c b := by
    intro c hc
    have hy : ∀ b, ∃ y, I.ev (N ^ 2) y = c b := fun b => (I.onto _ hM (c b)).1 (hc.1 b)
    choose y hy using hy
    refine ⟨y, fun mu hmu cm hcm i => ?_, hy⟩
    have h1 := hc.2 mu hmu cm hcm i
    refine (I.ker _ hM _).1 ?_
    have hfun : (fun j => I.ev (N ^ 2) (cm i j • y j)) = fun j => c j ≫ Xo.univ.t.act.act (cm i j) := by
      funext j
      simp only [I.lin, hy]
    rw [ev_sum I hM, hfun]
    exact h1
  obtain ⟨zz, -, -, hcover⟩ := ZCount.exists_class_representatives E H Dw n Λ N hΛ hN hle
  have hf : ∀ i, ∃ j, w i = fun b => I.ev (N ^ 2) (zz j b) := by
    intro i
    obtain ⟨y, hy, hyw⟩ := key (w i) (hw i)
    obtain ⟨j, hj⟩ := hcover y hy
    refine ⟨j, funext fun b => ?_⟩
    rw [← hyw b]
    exact evEq _ _ (hj b)
  choose f hf using hf

  have finj : Function.Injective f := by
    intro i i' h
    apply hinj
    rw [hf i, hf i', h]
  have fsurj : Function.Surjective f := Finite.surjective_of_injective finj
  obtain ⟨y, hy, hya⟩ := key a ha
  obtain ⟨j, hj⟩ := hcover y hy
  obtain ⟨i, rfl⟩ := fsurj j
  refine ⟨i, ?_⟩
  rw [hf i]
  funext b
  rw [← hya b]
  exact (evEq _ _ (hj b)).symm

end IsotropicEnum

open IsotropicEnum in

theorem isotropic_enumeration_onto_of_isLocalRing :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x0 z → (∀ a, InZh Xo Λ N a → ∃ i, z i = a) ∧ ∀ z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z' i)) → GeoInj Xo x0 z' → ∃ σ : Equiv.Perm (Fin (Λ.zCard N (Dw.p + Dw.q))), ∀ i, z' i = z (σ i) := by
  intro hL E _ _ _ H Dw l Xo T _ _ x0 n Λ N hΛ hN hle z hz hzi
  classical

  let ψ : T →+* AlgebraicClosure (IsLocalRing.ResidueField T) :=
    (algebraMap (IsLocalRing.ResidueField T) (AlgebraicClosure (IsLocalRing.ResidueField T))).comp
      (IsLocalRing.residue T)
  let g : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl
  have hA : ∀ (zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (zz i)) → GeoInj Xo x0 zz → ∀ a, InZh Xo Λ N a → ∃ i, zz i = a := by
    intro zz hzz hgi a ha
    obtain ⟨i, hi⟩ := exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x0) Λ hΛ hN hle
      (fun i b => g ≫ zz i b) (fun i => inZh_comp Xo Λ N g (hzz i)) (hgi _ ψ g rfl)
      (fun b => g ≫ a b) (inZh_comp Xo Λ N g ha)
    refine ⟨i, funext fun b => ?_⟩
    have hib : g ≫ zz i b = g ≫ a b := congrFun hi b

    obtain ⟨e, he, hiff⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo T x0 (N ^ 2) (pow_pos hN 2)
      (zz i b) (a b) ((hzz i).1 b) (ha.1 b)
    have hψ : ψ e = 1 := (hiff _ ψ).2 (congrArg (fun f => f.left) hib)
    have hmul : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he.eq, sub_self]
    have he1 : e = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
      · exact (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hmul)).symm
      · rw [(hu.mul_left_eq_zero).1 hmul, map_zero] at hψ
        exact absurd hψ zero_ne_one
    have hid := (hiff T (RingHom.id T)).1 (by rw [he1, map_one])
    have hsp : spMap (RingHom.id T) = 𝟙 _ := by simp [spMap]
    rw [hsp, Category.id_comp, Category.id_comp] at hid
    exact Over.OverMorphism.ext hid
  refine ⟨hA z hz hzi, fun z' hz' hzi' => ?_⟩
  have hsel : ∀ i, ∃ j, z j = z' i := fun i => hA z hz hzi (z' i) (hz' i)
  choose σ' hσ' using hsel
  have hinj' : Function.Injective z' := by
    intro i i' h
    apply hzi' _ ψ g rfl
    show (fun b => g ≫ z' i b) = fun b => g ≫ z' i' b
    rw [h]
  have σinj : Function.Injective σ' := by
    intro i i' h
    apply hinj'
    rw [← hσ' i, ← hσ' i', h]
  exact ⟨Equiv.ofBijective σ' ⟨σinj, Finite.surjective_of_injective σinj⟩, fun i => (hσ' i).symm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortSeriesValueTwistedEqConjugateValueStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortSeriesValue_twisted_eq_conjugate_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  first | exact @GlobalTheory.GalTw.shortValAt_conj | exact GlobalTheory.GalTw.shortValAt_conj | (intros; apply GlobalTheory.GalTw.shortValAt_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaExpressionEqOfWitnessesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExpression_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s (levPt Xo y1.x (x b)) (F1 b)) → FrMap φ2 y y2 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s (levPt Xo y2.x (x b)) (F2 b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ψ1 (thExpr Xo c nab y1 P F1) = ψ2 (thExpr Xo c nab y2 P F2) := by
  first | exact @GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses | exact GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses | (intros; apply GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_weight_triangular_frame : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), (P ∈ harmA c a n → ∀ (x : Fin n → Dw.La) (v : S), ThValAt Xo c nab y x P v → ThValAt Xo c nab y' x P (wchar (ex Dw a n) t * v)) ∧ (P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y v → ShortValAt Xo c nab w Λ β N P y' (wchar (ex Dw a n) t * v)) := by
  first | exact @GlobalTheory.thetaValue_weight | exact GlobalTheory.thetaValue_weight | (intros; apply GlobalTheory.thetaValue_weight <;> assumption)
end

