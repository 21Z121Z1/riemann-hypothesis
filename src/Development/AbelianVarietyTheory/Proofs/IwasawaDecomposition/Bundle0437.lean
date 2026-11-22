import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacter
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GloRhoZeroOfCompat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LevStd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem gloRho_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (z : Formalism.L2.Herm.intAf F E) :
    gloRho v spl halg z = e (resS F w z) := by
  obtain ⟨hz, h⟩ := he z
  rw [gloRho_apply]
  exact h

theorem gloRho_zero_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  intro a ha
  rw [gloRho_eq_of_compat v spl halg w e he, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem gloE_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (t : kP w) :
    gloE v spl halg w (gloRho_zero_of_compat v spl halg w e he) t = e t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← resS_oToS (F := F), gloE_resS, gloRho_eq_of_compat v spl halg w e he]

end GlobalTheory.Mem.LevStd

open GlobalTheory.Mem.LevStd in

theorem GlobalTheory.Mem.LevStd.levU_prod_glevH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (gp : Fin 2 → ℕ) (Jm : Matrix (Fin n) (Fin n) E) (S : StepLevel F E hc.sig Jm T f bad) (G : GLoc F E hc.sig gp) (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (lamw : ∀ w, Hw w →* ℂˣ) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → SG) (e : ∀ a v h, (𝓞 E ⧸ (wOf a v h).1.asIdeal) ≃+* kv F v), Jm = 1 → S.Lb = baseLb E n ST → ∀ hU : S.U = levU hc n ST SG (Subgroup.pi Set.univ Hw), (∀ x : S.U, S.chi x = ∏ w : SG, (lamw w ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 w, (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 w trivial⟩)⁻¹) → (∀ a v (_ : (gp a : 𝓞 F) ∈ v.asIdeal), v ∉ plUnder F ST) → (∀ a v h (w : SG), IsOver v w.1 ↔ w = wOf a v h) → (∀ φ : SG → ℂ, ∏ w : SG, φ w = ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), φ (wOf a v h)) → (∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F, IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z)) → (∀ a v h M, M ∈ Hw (wOf a v h) ↔ Matrix.GeneralLinearGroup.map (e a v h).toRingHom M ∈ H a v h) → (∀ a v h (M : Hw (wOf a v h)) (M' : H a v h), M'.1 = Matrix.GeneralLinearGroup.map (e a v h).toRingHom M.1 → lam a v h M' = lamw (wOf a v h) M) → ∃ V : GLevH S G H lam, ∀ a v h, V.fr a v h = 1 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG T f bad gp Jm S G Hw lamw H lam wOf e hJ hLb hU hchi hST hover hprod hcomp hH hlam
  subst hJ
  have hcomp' : ∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z) := hcomp
  have hw := fun a v h => gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hgE := fun a v h => gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hloc : ∀ v x, x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) →
      (x ∈ S.Uloc v ↔ x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v) := by
    intro v x hx
    constructor
    · intro hxv
      have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
      have hp : rll_put n v x ∈ S.U := by
        refine (S.U_eq _).2 ⟨rll_put_mem_UAd hc n v hxU, fun v' => ?_⟩
        by_cases hv : v' = v
        · subst hv; rw [rll_put_self]; exact hxv
        · rw [rll_put_ne n v v' hv]; exact Subgroup.one_mem _
      rw [hU] at hp
      exact ⟨_, hp, rll_put_self n v x⟩
    · rintro ⟨k, hk, rfl⟩
      rw [← hU] at hk
      exact ((S.U_eq k).1 hk).2 v
  have hxL : ∀ x : S.U, x.1 ∈ levU hc n ST SG (Subgroup.pi Set.univ Hw) := fun x => hU ▸ x.2
  have hkJ : ∀ x : S.U, x.1 ∈ J0 hc n ST := fun x => ((mem_levU hc n ST SG _).1 (hxL x)).1
  refine ⟨{ fr := fun _ _ _ => 1
            fr_lat := ?_
            mem := ?_
            red := fun a v h x => ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom
                ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 (wOf a v h)),
              (hH a v h _).1 ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 (wOf a v h) trivial)⟩
            red_eq := ?_
            chi_eq := ?_
            chi_unit := ?_ }, fun _ _ _ => rfl⟩
  · intro a v h x
    rw [hLb]
    exact gco_fr_lat n ST v (G.sp a v h) (G.sp_alg a v h) (hST a v h) x
  · intro a v h x hx
    rw [hLb] at hx
    have hG : ∀ y : GL (Fin n) (E ⊗[F] v.adicCompletion F), G.mat a v h 1 y =
        ((bc (gloPhi v (G.sp a v h)) y : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      intro y; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hloc v x hx, gco_mem_levLoc hc n ST SG v (G.sp a v h) (G.sp_alg a v h) Hw (wOf a v h) (hw a v h)
      ((hover a v h _).2 rfl) (fun w' hw' => (hover a v h w').1 hw') (hST a v h) x hx, hG]
    constructor
    · rintro ⟨M, hM, hMx⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom M, (hH a v h M).1 hM, ?_⟩
      rw [← hMx]
      ext i j
      rw [Matrix.map_apply, hgE]
      rfl
    · rintro ⟨M', hM', hM'x⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).symm.toRingHom M', (hH a v h _).2 ?_, ?_⟩
      · convert hM' using 1
        ext i j
        simp
      · rw [← hM'x]
        ext i j
        rw [Matrix.map_apply, hgE]
        simp
  · intro a v h x
    have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (hw a v h) (congruence_subgroup_le_stabilizer hc n ST (hkJ x))
    have hG : G.mat a v h 1 (bc (prV (E := E) v) x.1) =
        ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) x.1) : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hG, ← h1]
    ext i j
    rw [Matrix.map_apply, hgE]
    rfl
  · intro x
    rw [hchi x, Units.coe_prod]
    simp only [Units.val_inv_eq_inv_val]
    rw [hprod]
    congr 1; funext a; congr 1; funext v; congr 1; funext h
    rw [hlam a v h ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).1 (wOf a v h),
      (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).2 (wOf a v h) trivial⟩ _ rfl]
  · intro x
    rw [hchi x, Units.coe_prod, norm_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one]
    generalize (⟨_, _⟩ : Hw w) = m
    have hfo : IsOfFinOrder m := isOfFinOrder_of_finite m
    obtain ⟨N, hN, hpow⟩ := hfo.exists_pow_eq_one
    have hp : ((lamw w m : ℂˣ) : ℂ) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow, map_one, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one hp hN.ne'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvMapMulMapMulCancelComplexEmbedding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding {n : ℕ} {E : Type} [Field E] (f : E →+* ℂ) (γ : GL (Fin n) E) (M : Matrix (Fin n) (Fin n) ℂ) :
    ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f * ((γ : Matrix (Fin n) (Fin n) E).map f * M) = M := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul]
  simp

theorem GlobalTheory.Mem.Col2.TC.tr_eq_of_isTr : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY → ∀ (b : (I.stp u a i).β) (g : (I.stp u a i).G b) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i), IsTr (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) ((I.stp u a i).gam b g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E)) (eY s') (eY s) → (I.stp u a i).tr B.fields.emb B.embLL b g h s = B.embLL (((I.stp u a i).chr b g : B.LLˣ) : B.LL) * h s' := by
  intro B X I _ _ l Z u a i hi eY hId b g h s s' hT
  have key : s' = frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s := by
    apply Subtype.ext
    funext τ
    have h1 : s.1 τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z))
        (((I.stp u a i).gam b g : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E) τ * s'.1 τ := by
      have := hT τ
      rw [hId, hId] at this
      exact this
    have hf : embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := B.fields_embC τ
    show s'.1 τ = ((((I.stp u a i).gam b g)⁻¹ : GL _ _) : Matrix _ _ _).map (embAt B.embLL B.fields.emb τ) * s.1 τ
    rw [h1, hf]
    exact (GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding _ _ _).symm
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s) = _
  rw [← key]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DilPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_mk_iff {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (r : 𝓞 E) :
    HasRes P z (Ideal.Quotient.mk P.asIdeal r) ↔ Valued.v (z - algebraMap E _ (algebraMap (𝓞 E) E r)) < 1 := by
  constructor
  · rintro ⟨r', hr', h⟩
    have hm : r' - r ∈ P.asIdeal := Ideal.Quotient.eq.1 hr'
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r))) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    have e : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) =
        (z - algebraMap E _ (algebraMap (𝓞 E) E r')) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r)) := by
      simp only [map_sub]
      ring
    rw [e]
    exact Valuation.map_add_lt _ h h2
  · intro h
    exact ⟨r, rfl, h⟩

theorem hasRes_le_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P z c) : Valued.v z ≤ 1 := by
  obtain ⟨r, -, hr⟩ := h
  have h1 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : z = (z - algebraMap E _ (algebraMap (𝓞 E) E r)) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) := by
    ring
  rw [e]
  exact Valuation.map_add_le _ hr.le h1

theorem hasRes_lt_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (h : HasRes P z 0) : Valued.v z < 1 := by
  have := (hasRes_mk_iff (P := P) (z := z) 0).1 (by simpa using h)
  simpa using this

theorem last_sub_lt {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (Ki : Fin n → P.adicCompletion E)
    (D : Fin n → Fin n → P.adicCompletion E) (U : Fin n → P.adicCompletion E) (C : P.adicCompletion E)
    (hK : ∀ j, Valued.v (Ki j) ≤ 1) (hK' : ∀ j, j ≠ r → Valued.v (Ki j) < 1)
    (hD : ∀ j l, Valued.v (D j l) ≤ 1) (hDr : ∀ l, Valued.v (D r l - if l = r then C else 0) < 1)
    (hU : ∀ l, Valued.v (U l) ≤ 1) (hC : Valued.v C ≤ 1) :
    Valued.v ((∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j) < 1 := by
  have e : (∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j =
      ∑ j, Ki j * ((∑ l, D j l * U l) - C * U j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
  rw [map_mul]
  by_cases hj : j = r
  · subst hj
    have e2 : (∑ l, D j l * U l) - C * U j = ∑ l, (D j l - if l = j then C else 0) * U l := by
      simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e2]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (hK j)) ?_
    exact Valuation.map_sum_lt _ one_ne_zero fun l _ => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hU l)) (hDr l)
  · refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) (hK' j hj)
    refine Valuation.map_sub _ _ _ |>.trans (max_le ?_ ?_)
    · exact Valuation.map_sum_le _ fun l _ => by
        rw [map_mul]
        exact mul_le_one' (hD j l) (hU l)
    · rw [map_mul]
      exact mul_le_one' hC (hU j)

theorem pullbackVector_triple_mul {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * δ * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem pullbackVector_mul_right {n : ℕ} (y k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

theorem adAt_pullV_triv {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (x : Sp E n) (i : Fin n) :
    adAt F w (GlobalTheory.Mem.Col2.pullV (y * δ * k) x i) = adAt F w (GlobalTheory.Mem.Col2.pullV (y * k) x i) := by
  rw [pullbackVector_triple_mul, pullbackVector_mul_right]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ht, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem adeleComponentAt_triple_mul_dilation_trivial {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (i j : Fin n) :
    adAt F w ((y * δ * k : GL (Fin n) (AfE F E)).1 i j) = adAt F w ((y * k : GL (Fin n) (AfE F E)).1 i j) := by
  have h1 : ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    ext a b
    rw [Matrix.map_apply, ht, Matrix.one_apply]
  have h2 : (δ : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    have e : (δ : Matrix (Fin n) (Fin n) (AfE F E)) * ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) (AfE F E) => M.map (adAt F w)) e
    simp only [Matrix.map_mul, h1, mul_one, Matrix.map_one (adAt F w) (map_zero _) (map_one _)] at this
    exact this
  have e : ((y * δ * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
      ((y * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) := by
    simp only [Units.val_mul, Matrix.map_mul, h2, mul_one]
  exact congrArg (fun M => M i j) e

theorem isPointOf_last_coordinate_dilation_one_prime_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (y δ k : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (P : ST) (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) (b : 𝓞 E ⧸ P.1.asIdeal), IsPtOf hc (y * k) p → k ∈ Formalism.L2.Herm.UstdAf hc n → δ ∈ Formalism.L2.Herm.UstdAf hc n → Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, δ.1 i j ∈ RInt F E) → (∀ i j, (δ⁻¹).1 i j ∈ RInt F E) → (∀ w : HeightOneSpectrum (𝓞 E), (w ∈ SG ∨ w ∈ Q ∨ (w ∈ ST ∧ w ≠ P.1)) → ∀ i j, adAt F w ((δ⁻¹).1 i j) = if i = j then 1 else 0) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j)) (if j = r then b else 0)) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((δ⁻¹).1 r j)) (if j = r then (c : 𝓞 E ⧸ P.1.asIdeal) else 0)) → p'.deco = DecoSet.dia1 P c p.deco → p'.fr = p.fr → IsPtOf hc (y * δ * k) p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q y δ k p p' P c b h hk hδ hkc hδi hδi' htriv hkr hδr hdeco hfr
  classical
  have hy : y ∈ Formalism.L2.Herm.UstdAf hc n := by
    have := mul_mem h.uni (inv_mem hk)
    rwa [mul_inv_cancel_right] at this
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hδI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E := by
    intro z
    constructor
    · intro hz i
      exact PtExist.mulVec_int hδi' hz i
    · intro hz i
      have := PtExist.mulVec_int hδi hz i
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  have hN : p'.deco.1.N = p.deco.1.N := by rw [hdeco]; rfl
  have hbe : p'.deco.1.be = p.deco.1.be := by rw [hdeco]; rfl
  have hf : ∀ (P' : ST) (x : Sp E n), p'.deco.1.f P' x =
      ((Pi.mulSingle (M := fun Q : ST => (𝓞 E ⧸ Q.1.asIdeal)ˣ) P c P' : (𝓞 E ⧸ P'.1.asIdeal)ˣ) : 𝓞 E ⧸ P'.1.asIdeal) * p.deco.1.f P' x := by
    intro P' x
    rw [hdeco]
    rfl
  have hu : ∀ x ∈ p.deco.1.N, ∀ l, GlobalTheory.Mem.Col2.pullV y x l ∈ RInt F E := by
    intro x hx
    refine (hkI _).2 ?_
    rw [← pullbackVector_mul_right]
    exact (mem_latS_std _).1 ((h.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
  refine ⟨mul_mem (mul_mem hy hδ) hk, fun z => ?_, fun P' x hx i hi => ?_, fun w x hx i => ?_, fun P' i j => ?_⟩
  · rw [hN]
    refine (h.lat z).trans ((mem_latS_std _).trans (Iff.trans ?_ (mem_latS_std _).symm))
    have e1 : ((y * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    have e2 : ((y * δ * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z)) := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    rw [e1, e2]
    exact (hkI _).symm.trans ((hδI _).trans (hkI _))
  · rw [hN] at hx
    have hv := h.f P' x hx i hi
    rw [hf]
    by_cases hPP : P' = P
    · subst hPP
      rw [Pi.mulSingle_eq_same]
      obtain ⟨s, hs, hv'⟩ := hv
      obtain ⟨cr, hcr⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 E ⧸ P'.1.asIdeal)
      rw [← hs, ← hcr, ← map_mul, hasRes_mk_iff]
      have hint : ∀ a ∈ RInt F E, Valued.v (adAt F P'.1 a) ≤ 1 := fun a ha => (mem_rInt_iff F E a).1 ha P'.1
      have hCle : Valued.v (algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr)) ≤ 1 := by
        rw [valued_algebraMap]
        exact HeightOneSpectrum.valuation_le_one _ _
      have key := last_sub_lt i (fun j => adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j))
        (fun j l => adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l))
        (fun l => adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) (algebraMap E _ (algebraMap (𝓞 E) E cr))
        (fun j => hasRes_le_one (hkr i j hi))
        (fun j hj => by
          have := hkr i j hi
          rw [if_neg hj] at this
          exact hasRes_lt_one this)
        (fun j l => hint _ (hδi' j l))
        (fun l => by
          have := hδr i l hi
          by_cases hl : l = i
          · rw [if_pos hl, ← hcr, hasRes_mk_iff] at this
            rw [if_pos hl]
            exact this
          · rw [if_neg hl] at this
            rw [if_neg hl, sub_zero]
            exact hasRes_lt_one this)
        (fun l => hint _ (hu x hx l)) hCle
      rw [pullbackVector_mul_right] at hv'
      rw [pullbackVector_triple_mul]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at hv' key ⊢
      have e : (∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s) =
          ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) +
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) -
              algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s)) := by ring
      rw [e]
      refine Valuation.map_add_lt _ key ?_
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hCle) hv'
    · rw [Pi.mulSingle_eq_of_ne hPP, Units.val_one, one_mul,
        adAt_pullV_triv y δ k P'.1 (htriv P'.1 (Or.inr (Or.inr ⟨P'.2, fun e => hPP (Subtype.ext e)⟩))) x i]
      exact hv
  · rw [hN] at hx
    rw [hbe, adAt_pullV_triv y δ k w.1 (htriv w.1 (Or.inl w.2)) x i]
    exact h.be w x hx i
  · rw [hfr, adeleComponentAt_triple_mul_dilation_trivial y δ k P'.1 (htriv P'.1 (Or.inr (Or.inl P'.2))) i j]
    exact h.fr P' i j

end GlobalTheory.Mem.Col2.DilPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section
namespace GlobalTheory.Mem.Col2.RatMove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ}

omit [NumberField E] [StarRing E] in

theorem glEquiv_apply_mulVec (g : GL (Fin n) E) (x : Sp E n) : Formalism.UG.glEquiv g x = (g : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [Formalism.UG.glEquiv]

theorem ufGL_eq (γ : UF E n) : ufGL E n γ = (((ratEquiv hc n).symm γ : URat hc n) : GL (Fin n) E) := by
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext i
  have h1 := congrArg (fun g : UF E n => (g : Sp E n ≃ₗ[E] Sp E n) (Pi.single j 1) i) hγ
  simp only [ratHom, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  rw [← glEquiv_apply_mulVec, ← glEquiv_apply_mulVec, h1]
  show Formalism.UG.glEquiv (toGLm E n γ.1) _ i = _
  rw [glEquiv_toGLm]

omit [NumberField E] [StarRing E] in

theorem glEquiv_symm_apply (γ : GL (Fin n) E) (v : Sp E n) :
    (Formalism.UG.glEquiv γ).symm v = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v := by
  rw [LinearEquiv.symm_apply_eq]
  simp [Formalism.UG.glEquiv, Matrix.mulVec_mulVec]

theorem pullV_ratMul (γ : GL (Fin n) E) (g : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (Formalism.UG.bc (iA F E) γ * g) x = GlobalTheory.Mem.Col2.pullV g ((Formalism.UG.glEquiv γ).symm x) := by
  have h := Formalism.L2.Col.pullV_rawSm γ g 1 x
  rw [inv_one, mul_one, Units.val_one, Matrix.one_mulVec] at h
  rw [glEquiv_symm_apply]
  exact h

variable {hc} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem isPtOf_ratMul (γ : URat hc n) {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    IsPtOf hc (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
      (((ratHom hc n γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]
    ext w
    refine (h.lat _).symm.trans ?_
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hst : (1 : GL (Fin n) (AfE F E))⁻¹ ∈
      Formalism.UG.stabGL (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by
    rw [inv_one]; exact one_mem _
  have hN2 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) (stdLat E n) γ g _ hst
  rw [inv_one, mul_one] at hN2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (ratIn hc n γ).2 h.uni
  · have hc2 := PtExist.carries_globLat (F := F) (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
    rw [hN2, hN] at hc2
    exact hc2
  · intro P x hx i hi
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    rw [pullV_ratMul]
    exact h.f P _ hx' i hi
  · intro w x hx i
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    show HasRes w.1 _ (((((1 : GLG E n SG) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) *ᵥ
      p.deco.1.be w ((Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x)) i)
    rw [Pi.one_apply, Units.val_one, Matrix.one_mulVec, pullV_ratMul]
    exact h.be w _ hx' i
  · intro P i j
    show _ = algebraMap E _ ((Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * (((1 : GLQ E n Q) P)⁻¹).1) (Pi.single j 1) i)
    have e1 : (((1 : GLQ E n Q) P)⁻¹).1 = 1 := by simp
    rw [e1, mul_one, LinearEquiv.mul_apply, glEquiv_apply_mulVec, Units.val_mul, Matrix.mul_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.fr P l j]
    congr 1
    show adAt F P.1 (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ : GL (Fin n) E) i l)) = _
    rw [adAt_inclE]

theorem isPtOf_ratAd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E))
    (p : DecoF E n ST SG Q), IsPtOf hc g p →
      IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  intro F E _ _ _ _ _ _ hc n ST SG Q γ g p h
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  have hR : ratAd F γ = Formalism.UG.bc (iA F E) ((((ratEquiv hc n).symm γ : URat hc n)) : GL (Fin n) E) := by
    show Formalism.UG.bc (iA F E) (ufGL E n γ) = _
    rw [ufGL_eq hc]
  have := isPtOf_ratMul ((ratEquiv hc n).symm γ) (ST := ST) (SG := SG) (Q := Q) h
  rw [hγ] at this
  rw [hR]
  exact this

end GlobalTheory.Mem.Col2.RatMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_maximalCompact_fock_substitution_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (p q : D.what₂.Tau → ℕ), (∀ τ, p τ + q τ = T.rank) → (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ P : PolF D T.rank S.rank, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹) (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) P) := by
  first | exact @GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact | exact GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact | (intros; apply GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact <;> assumption)
end

