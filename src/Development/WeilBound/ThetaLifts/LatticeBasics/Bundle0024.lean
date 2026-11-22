import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0002
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.MemIntLocOfIdem
import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0002

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.CompCA
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Vf2

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas GlobalTheory.Doubling PositivityTheory.ThKG.Loc.Cone.Vf
open Formalism.UG (bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

variable (σ v) in

def cInt : intLoc F E v →+* intLoc F E v :=
  ((sigR (Fv F v) σ).comp (intLoc F E v).subtype).codRestrict _ fun z => sigR_mem_intLoc σ z.2

theorem exists_res {B : Base F E} (hB : B.IsGood σ) (v : Pl F) : ∃ (K : Type) (_ : Field K) (r : intLoc F E v →+* K),
    Function.Surjective r ∧ (((∀ z, r z = 0 → r (cInt σ v z) = 0) ∧ ∃ κ, r (κ - cInt σ v κ) ≠ 0) ∨
      ∃ η, r η = 1 ∧ r (cInt σ v η) = 0) ∧ ∀ z, r z ≠ 0 → r (cInt σ v z) ≠ 0 → IsUnit z := by
  have hσ := hB.cm
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · let ρ : intLoc F E v →+* v.adicCompletionIntegers F := ((splitProj τ : Fv F v ⊗[F] E →+* Fv F v).comp
      (intLoc F E v).subtype).codRestrict (v.adicCompletionIntegers F).toSubring fun z => splitProj_mem τ z.2
    have mk : ∀ a b : v.adicCompletionIntegers F, (splitAlgEquiv hσ τ).symm (a.1, b.1) ∈ intLoc F E v := fun a b =>
      (mem_intLoc_iff_split hσ τ).2 ⟨by rw [splitProj_symm]; exact a.2, by rw [splitProj_comp_symm]; exact b.2⟩
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ,
      IsLocalRing.residue_surjective.comp fun a => ⟨⟨_, mk a 0⟩, Subtype.ext (splitProj_symm hσ τ _)⟩,
      .inr ⟨⟨_, splitIdem_mem hσ τ⟩, ?_, ?_⟩, fun z h1 h2 => ?_⟩
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext (splitProj_splitIdem hσ τ) : ρ ⟨_, splitIdem_mem hσ τ⟩ = 1)).trans (map_one _)
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext ((splitProj_comp τ σ _).symm.trans (splitProj_comp_splitIdem hσ τ)) :
        ρ (cInt σ v ⟨_, splitIdem_mem hσ τ⟩) = 0)).trans (map_zero _)
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨b, hb⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h2).exists_right_inv
      refine IsUnit.of_mul_eq_one ⟨_, mk a b⟩ (Subtype.ext (split_ext hσ τ ?_ ?_))
      · rw [Subring.coe_mul, map_mul, splitProj_symm, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
      · rw [Subring.coe_mul, map_mul, splitProj_comp_symm, Subring.coe_one, map_one, splitProj_comp]; exact congrArg Subtype.val hb
  · have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
    obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
    obtain ⟨ϖ, -, hv, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hσ hw hc
    let ρ : intLoc F E v →+* w.adicCompletionIntegers E :=
      ((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z => toCompl_mem hu z.2
    have sj : Function.Surjective ρ := fun a => by
      obtain ⟨z, hz⟩ := (toCompl_bijective hw hu).2 a.1
      exact ⟨⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ a.2)⟩, Subtype.ext hz⟩
    have un : ∀ z, ((IsLocalRing.residue _).comp ρ) z ≠ 0 ↔ Valued.v (toCompl hu z.1) = 1 := fun z =>
      (IsLocalRing.residue_ne_zero_iff_isUnit _).trans HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ, IsLocalRing.residue_surjective.comp sj,
      .inl ⟨fun z hz => by_contra fun h => (un z).2 ?_ hz, ?_⟩, fun z h1 _ => ?_⟩
    · rw [← hv, hc]
      exact (un (cInt σ v z)).1 h
    · obtain ⟨κ, hκ⟩ := sj ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩
      refine ⟨κ, (un _).2 ?_⟩
      change Valued.v (toCompl hu (κ.1 - sigR _ σ κ.1)) = 1
      rw [map_sub, ← hc, show toCompl hu κ.1 = x from congrArg Subtype.val hκ, Valuation.map_sub_swap, hx1]
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨z', rfl⟩ := sj a
      refine IsUnit.of_mul_eq_one z' (Subtype.ext ((toCompl_bijective hw hu).1 ?_))
      rw [Subring.coe_mul, map_mul, Subring.coe_one, map_one]; exact congrArg Subtype.val ha

theorem fr_iff {X : Spc F E n} {a : GL (Fin n) (Fv F v ⊗[F] E)}
    (ha : ∀ y : Fin n → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F X.L v) (M) :
    M ∈ Pres v X ↔ ∃ N : Matrix (Fin n) (Fin n) (intLoc F E v), (intLoc F E v).subtype.mapMatrix N = fr v a M := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) (AE F E)) y, compFin F E v ∘ (M *ᵥ y) = M.map (compFin F E v) *ᵥ (compFin F E v ∘ y) :=
    fun M y => funext fun i => RingHom.map_mulVec _ M y i
  have co : ∀ z ∈ latLoc F X.L v, ∀ i, ((a⁻¹).1 *ᵥ z) i ∈ intLoc F E v := fun z hz =>
    (ha _).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
  refine ⟨fun hM => ?_, ?_⟩
  · have : ∀ i j, fr v a M i j ∈ intLoc F E v := fun i j => by
      let z := a.1 *ᵥ fun k => (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) k j
      have hz : z ∈ latLoc F X.L v := (ha _).1 fun k => by
        rw [Matrix.one_apply]; split_ifs
        exacts [one_mem _, zero_mem _]
      have ey : compFin F E v ∘ (fun i => sgE E v (z i)) = z := funext fun i => comp_sgE _
      have h1 := ((mem_latW_loc X _).1 (hM _ ((mem_latW_loc X (fun i => sgE E v (z i))).2
        ⟨fun u hu => funext fun i => at_sgE _ u hu, ey.symm ▸ hz⟩))).2
      have h2 := co _ h1 i
      rw [mv, ey, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h2
      change (fr v a M * 1 : Matrix _ _ _) i j ∈ _ at h2
      rwa [Matrix.mul_one] at h2
    exact ⟨fun i j => ⟨_, this i j⟩, rfl⟩
  · rintro ⟨N, hN⟩ y hy
    obtain ⟨h1, h2⟩ := (mem_latW_loc X y).1 hy
    refine (mem_latW_loc X _).2 ⟨at_mulVec_right _ h1, ?_⟩
    have := (ha (fr v a M *ᵥ ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)))).1 fun i => by
      rw [← hN]
      change ∑ j, (N i j).1 * ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)) j ∈ _
      exact sum_mem fun j _ => mul_mem (N i j).2 (co _ h2 j)
    rwa [fr_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← mv] at this

omit [NumberField E] in
theorem comp_cA (z : AE F E) : compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gram_fr (a : GL (Fin n) (Fv F v ⊗[F] E)) (J M m : Matrix (Fin n) (Fin n) (AE F E)) :
    a.1ᵀ * (Mᵀ * J * m.map (cA σ)).map (compFin F E v) * a.1.map (sigR _ σ) =
      (fr v a M)ᵀ * (a.1ᵀ * J.map (compFin F E v) * a.1.map (sigR _ σ)) * (fr v a m).map (sigR _ σ) := by
  have e1 : (a⁻¹).1ᵀ * a.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have e2 : a.1.map (sigR _ σ) * (a⁻¹).1.map (sigR _ σ) = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 : (m.map (cA σ)).map (compFin F E v) = (m.map (compFin F E v)).map (sigR _ σ) := Matrix.ext fun _ _ => comp_cA _
  rw [fr_apply, fr_apply, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    e3, Matrix.transpose_map]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (a⁻¹).1ᵀ, e1, Matrix.one_mul, ← Matrix.mul_assoc (a.1.map _), e2, Matrix.one_mul]

theorem exists_beta {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s)
    (g : UG (cA σ) (dbl (incM F X.J))) {x y a₁ a₂ : Matrix (Fin n) (Fin n) (AE F E)}
    (hg : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows x y) (hx : x ∈ Pres v X) (hy : y ∈ Pres v X)
    (h1 : a₁ ∈ Pres v X) (h2 : a₂ ∈ Pres v X) (h : a₁ * x + a₂ * y = 1) (ax : At (evFin F v) (x - 1)) (ay : At (evFin F v) (y - 1)) :
    ∃ b b' t', Adj (cA σ) (incM F X.J) b b' ∧ b + b' = -1 ∧ b ∈ Pres v X ∧ t' ∈ Pres v X ∧ (y + b * (y - x)) * t' = 1 := by
  have hσ := cm_conj_conj hB.cm
  have cc := cA_cA (F := F) hσ
  have hL := hX.lat
  obtain ⟨K, _, ρ, r1, r2, r3⟩ := exists_res hB v
  obtain ⟨P, p1, p2⟩ := Frames.exists_rational_frame X.L v
  obtain ⟨G', hG', g1, g2⟩ := Hgt.gram_loc (v := v) (herm_det hX).ne_zero hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) hX.dual
    isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P p1 p2
  simp only [inv_one, one_mul] at g1 g2
  have ha := fr_iff (Frames.frame_of_rational P p1 p2)
  set G₀ := P.1ᵀ * X.J * P.1.map σ with hG₀
  let ι := inclR (F := F) (E := E) (Fv F v)
  set a : GL (Fin n) (Fv F v ⊗[F] E) := bc ι P
  let j := (intLoc F E v).subtype.mapMatrix (m := Fin n)
  have inj : Function.Injective j := fun A B e => Matrix.ext fun i k => Subtype.ext (congrFun₂ e i k)
  let G : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g1 i k).mem⟩
  let H : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g2 i k).mem⟩
  have eG : a.1ᵀ * (incM F X.J).map (compFin F E v) * a.1.map (sigR _ σ) = j G := by
    change _ = G₀.map ι
    rw [hG₀, Matrix.map_mul, Matrix.map_mul, show (incM F X.J).map (compFin F E v) = X.J.map ι from
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] X.J i k) (map_one (evFin F v))]
    rfl
  have jj : ∀ N N' : Matrix (Fin n) (Fin n) (intLoc F E v), j (Nᵀ * G * N'.map (cInt σ v)) = (j N)ᵀ * j G * (j N').map (sigR _ σ) :=
    fun N N' => by rw [map_mul, map_mul]; rfl
  obtain ⟨θ₀, hθ⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  let θ : AE F E := inclR (F := F) (AF F) (θ₀ : E)
  have iθ : compFin F E v (-θ) ∈ intLoc F E v := by
    rw [map_neg]; exact neg_mem (tmul_mem_intLoc (show evFin F v 1 ∈ _ by rw [map_one]; exact one_mem _) θ₀)
  have b0 : Adj (cA σ) (incM F X.J) ((-θ) • 1) ((-cA σ θ) • 1) := Adj.one.smul (by rw [map_neg, cc])
  have hb0 : (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (-cA σ θ) • 1 = -1 := by
    rw [← add_smul, ← neg_add, show θ + cA σ θ = inclR (F := F) (AF F) (θ₀ + σ θ₀ : E) from (map_add _ _ _).symm, hθ, map_one,
      neg_smul, one_smul]
  have pb0 := smul_mem_Pres hL iθ (one_mem (Pres v X))
  have lag := lag_of b0 hb0 g hg
  set b₀ := (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E))
  have pm := sub_mem hy hx
  obtain ⟨Nm, hNm⟩ := (ha _).1 pm
  obtain ⟨NM, hNM⟩ := (ha _).1 (add_mem hy (mul_mem pb0 pm))
  obtain ⟨NP, hNP⟩ := (ha _).1 (add_mem h1 h2)
  obtain ⟨NQ, hNQ⟩ := (ha _).1 (sub_mem (neg_mem h1) (mul_mem (add_mem h1 h2) pb0))
  obtain ⟨S, s1, s2⟩ := exists_skew (c := cInt σ v) (r := ρ) (G := G) (G' := H) (M := NM) (m := Nm) (P := NP) (Q := NQ)
    (fun z => Subtype.ext (by
      change sigR _ σ (sigR _ σ z.1) = z.1
      induction z.1 using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
      | add x y hx hy => simp only [map_add, hx, hy])) r1
    (fun i k => Subtype.ext (congrArg ι (by
      change σ (G₀ k i) = G₀ i k
      simp only [hG₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hX.herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)))
    (inj (by
      rw [map_mul, map_one]
      change G₀.map ι * G'.map ι = 1
      rw [← Matrix.map_mul, mul_eq_one_comm.1 hG', Matrix.map_one _ (map_zero _) (map_one _)])) r2 r3
    (inj (by
      rw [map_add, jj, jj, hNm, hNM, ← eG, ← gram_fr, ← gram_fr, ← Matrix.add_mul, ← Matrix.mul_add,
        ← Matrix.map_add _ (map_add _), lag, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, map_zero]))
    (inj (by
      rw [map_add, map_mul, map_mul, hNm, hNM, hNP, hNQ, ← map_mul, ← map_mul, ← map_add, map_one, ← map_one (fr v a), ← h]
      congr 1
      noncomm_ring))
  let SA : Matrix (Fin n) (Fin n) (AE F E) := (a.1 * j S * (a⁻¹).1).map (sgE E v)
  have aS : At (evFin F v) SA := fun u hu => Matrix.ext fun i k => at_sgE _ u hu
  have fS : fr v a SA = j S := by
    rw [fr_apply, show SA.map (compFin F E v) = a.1 * j S * (a⁻¹).1 from Matrix.ext fun _ _ => comp_sgE _]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  have sk : SAᵀ * incM F X.J + incM F X.J * SA.map (cA σ) = 0 := by
    have k1 := gram_fr (σ := σ) a (incM F X.J) SA 1
    have k2 := gram_fr (σ := σ) a (incM F X.J) 1 SA
    have k3 := congrArg j s1
    have k4 := jj S 1
    have k5 := jj 1 S
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, map_one, mapc_one, fS, eG,
      Matrix.map_one _ (map_zero (sigR (Fv F v) σ)) (map_one _), Matrix.map_one _ (map_zero (cInt σ v)) (map_one _)] at k1 k2 k4 k5
    rw [map_add, k4, k5, ← k1, ← k2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add _), map_zero] at k3
    have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
    have u2 : IsUnit (a.1.map (sigR (Fv F v) σ)) := a.isUnit.map (sigR (Fv F v) σ).mapMatrix
    rw [u2.mul_left_eq_zero, u1.mul_right_eq_zero] at k3
    refine Matrix.ext fun i k => eq_zero_of_at (v := v) (fun u hu => congrFun₂ (at_add (at_mul_left (M := SAᵀ)
      (fun u hu => congrArg Matrix.transpose (aS u hu)) _) (at_mul_right _ (N := SA.map (cA σ)) fun u hu => Matrix.ext fun i k => by
        change u • cA σ (SA i k) = 0
        rw [← map_smul, show u • SA i k = 0 from congrFun₂ (aS u hu) i k, map_zero]) u hu) i k) (congrFun₂ k3 i k)
  have am : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  obtain ⟨t', pt, ht⟩ := exists_inv ha (f := y + (b₀ + SA) * (y - x)) (N := NM + S * Nm)
    (by rw [add_sub_right_comm]; exact at_add ay (at_mul_right _ am))
    (by rw [map_add, map_mul, hNm, hNM, ← fS, ← map_mul, ← map_add, add_mul, add_assoc]) s2
  exact ⟨b₀ + SA, _ + -SA, t', b0.add (by rw [Adj, mapc_neg, Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left sk),
    by rw [add_add_add_comm, add_neg_cancel, add_zero, hb0], add_mem pb0 ((ha _).2 ⟨S, fS.symm⟩), pt, ht⟩

end GlobalTheory.ThK.Dbl.Vf2

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ConvOfCpt
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W} {r s r' s' : ℕ}

theorem conv_of_cpt (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) : ∀ Φ ∈ schA F _, M.Conv o Φ := by
  intro Φ hΦ h
  obtain ⟨t1, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  have hc : Continuous fun g => theta o Φ g h := t1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := c.bdd hc fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h
  exact Measure.integrableOn_of_bounded (M := C) (c.fin _ _ p.good.haar p.good.dom).ne hc.aestronglyMeasurable
    (Eventually.of_forall hC)

theorem I_lin (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (a : ℂ) : M.I o (Φ + a • Ψ) = M.I o Φ + a • M.I o Ψ := by
  funext h
  have e : ∀ g, theta o (Φ + a • Ψ) g h = theta o Φ g h + a * theta o Ψ g h := fun g => by
    simp only [theta, map_add, map_smul]
    rw [thetaSum_add F (p.weil.isUSplitting.pres _ _ hΦ) (Submodule.smul_mem _ _ (p.weil.isUSplitting.pres _ _ hΨ)),
      thetaSum_smul]
  simp only [Model.I, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (conv_of_cpt hT p c _ hΦ h) ((conv_of_cpt hT p c _ hΨ h).const_mul a), integral_const_mul]

theorem pol_sch (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun _ h => h.1.trans h.2)

theorem int_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (h : IsFundamentalDomain Γ D μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in D, f (x * g) ∂μ = ∫ x in D, f x ∂μ := by
  have h' : IsFundamentalDomain Γ ((fun x => x * g) '' D) μ := by
    simpa [← Set.image_smul] using h.smul_of_comm (MulOpposite.op g)
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (Homeomorph.mulRight g).measurableEmbedding f D]
  exact h'.setIntegral_eq h fun γ x => hf γ γ.2 x

theorem I_act (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (g : UA σ Y.J) : M.I o (o (g, 1) Φ) = M.I o Φ := by
  funext h
  obtain ⟨-, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  haveI := c.cnt
  haveI := p.good.haar
  haveI := c.right _ p.good.haar
  have e : ∀ x, theta o (o (g, 1) Φ) x h = theta o Φ (x * g) h := fun x => by
    rw [theta, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact int_right p.good.dom (fun x => theta o Φ x h)
    (fun γ hγ x => by simpa using t2 γ hγ 1 (one_mem _) x h) g

theorem upd_sb {v : Pl F} {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {z} (hz : z ∈ SB _) (u : Pl F) :
    Function.update φ v z u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h u

theorem upd_cof {v : Pl F} {φ φ' : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = φ' u) (z) :
    ∀ᶠ u in cofinite, Function.update φ v z u = φ' u :=
  (h.and (eventually_cofinite_ne v)).mono fun _ e => by rw [Function.update_of_ne e.2]; exact e.1

theorem I_aug (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) (v : Pl F) (f : SInf F (Fin n × Fin d))
    {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    {z₀ z} (h0 : z₀ ∈ SB _) (hz : z ∈ augAt o v) :
    M.I o (pure f (Function.update φ v (z₀ + z))) = M.I o (pure f (Function.update φ v z₀)) := by
  have h3 := (h2.and p.good.std).mono fun _ h => h.1.trans h.2
  obtain ⟨t, ht, ht'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h3
  have mem : ∀ z ∈ SB _, pure f (Function.update φ v z) ∈ schA F _ := fun z hz =>
    GlobalTheory.TensUniq.pure_mem_schA f _ (upd_sb h1 hz) (upd_cof h3 z)
  have add : ∀ z ∈ SB _, ∀ z' ∈ SB _, ∀ a : ℂ, M.I o (pure f (Function.update φ v (z + a • z'))) =
      M.I o (pure f (Function.update φ v z)) + a • M.I o (pure f (Function.update φ v z')) := fun z hz z' hz' a => by
    rw [← I_lin hT p c (mem z hz) (mem z' hz'), ← ht', ← ht', ← ht']
    congr 1
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have zero : M.I o (pure f (Function.update φ v 0)) = 0 := by
    have := add 0 (zero_mem _) 0 (zero_mem _) (-1)
    simpa using this
  have key : z ∈ SB _ ∧ M.I o (pure f (Function.update φ v z)) = 0 := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, -, x, hx, y, hy, a, rfl⟩ := hz
      refine ⟨sub_mem hy hx, ?_⟩
      have e := a t ⟨ht, ht' x ▸ mem x hx⟩
      rw [ht', ht'] at e
      rw [sub_eq_add_neg, ← neg_one_smul ℂ x, add y hy x hx, ← e, I_act hT p c (mem x hx)]
      simp
    | zero => exact ⟨zero_mem _, zero⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by simpa [hx.2, hy.2] using add x hx.1 y hy.1 1⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ _ hx.1, by simpa [hx.2, zero] using add 0 (zero_mem _) x hx.1 a⟩
  simpa [key.2] using add z₀ h0 z key.1 1

theorem toSo_of (hR : KReal) (hF : KFin) (hK : KCoinv) (hT : ThetaBasic) (hC : CptAll) : ToSo := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h hq Φ' hΦ
  obtain ⟨R, hr⟩ := hR F E σ B a a' G X om om' h
  obtain ⟨Rf, hf⟩ := hF F E σ B a a' G X om om' h
  obtain ⟨-, k1, k2, -⟩ := (hK F E σ B a a' G X om om' R Rf ⟨h, hr, hf⟩).1 _ h.chars.good
  have p := pairV' h
  have c := hC F E σ B _ _ _ _ h.base (.inl p.herm) (by omega)
  have le := pol_sch p.good
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hz
    obtain ⟨y, hy, e⟩ := k2 B.τ₁ (Rf.p' _ (φ B.v₁))
    refine ⟨pure f (Function.update φ B.v₁ y), ⟨Submodule.subset_span ⟨f, hf, _, upd_sb h1 hy.1, upd_cof h2 y, rfl⟩,
      Submodule.subset_span ⟨f, _, upd_sb h1 hy.1, upd_cof h2 y, by rwa [Function.update_self], rfl⟩⟩, ?_⟩
    have := I_aug hT p c B.v₁ f h1 h2 hy.1 ((k1 _ (sub_mem (h1 _) hy.1)).1 (by rw [map_sub, e, sub_self]))
    rw [← this, add_sub_cancel, Function.update_eq_self]
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y hx hy ix iy =>
    obtain ⟨x', mx, ex⟩ := ix
    obtain ⟨y', my, ey⟩ := iy
    refine ⟨x' + y', add_mem mx my, ?_⟩
    rw [← one_smul ℂ y, ← one_smul ℂ y', I_lin hT p c (le mx.1) (le my.1), I_lin hT p c (le hx) (le hy), ex, ey]
  | smul t x hx ix =>
    obtain ⟨x', mx, ex⟩ := ix
    refine ⟨t • x', Submodule.smul_mem _ _ mx, ?_⟩
    rw [← zero_add (t • x), ← zero_add (t • x'), I_lin hT p c (zero_mem _) (le mx.1), I_lin hT p c (zero_mem _) (le hx), ex]

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global

attribute [local instance 100000] measurableSpace_adeleRing

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
  {Φ : (κ ⊕ κ → AF F) → ℂ}

theorem sl_int (h : Φ ∈ schA F (κ ⊕ κ)) (a) : Integrable (sl a Φ) (adeleMeasurePi F) :=
  integrable_of_mem_schwartzBruhatPi ((sl_mem h).1 a)

variable (F κ) in

def lD : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (LinearMap.exists_extend
  ({ toFun Φ := adelicFourierPi F (sl 0 Φ.1) 0
     map_add' Φ Ψ := congrFun (adelicFourierPi_add (sl_int Φ.2 0) (sl_int Ψ.2 0)) 0
     map_smul' c Φ := congrFun (adelicFourierPi_smul c (sl 0 Φ.1)) 0 } : schA F (κ ⊕ κ) →ₗ[ℂ] ℂ)).choose

theorem lD_apply (h : Φ ∈ schA F (κ ⊕ κ)) : lD F κ Φ = adelicFourierPi F (sl 0 Φ) 0 :=
  LinearMap.congr_fun (LinearMap.exists_extend _).choose_spec (⟨Φ, h⟩ : schA F (κ ⊕ κ))

theorem lD_int (h : Φ ∈ schA F (κ ⊕ κ)) : lD F κ Φ = ∫ u, Φ (Sum.elim u u) ∂adeleMeasurePi F := by
  rw [lD_apply h]; simp [adelicFourierPi, sl]

theorem lD_adm : lD F κ ∈ (adeleClass F).adm (κ ⊕ κ) := fun g hg => by
  refine ⟨finiteFourierPi F (fun u => g (Sum.elim (u + finPartPi (K := F) 0) u)) (finPartPi 0) •
    ((BoundedContinuousFunction.evalCLM ℂ (infPartPi 0)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp
      ((mixedFourierPiSchwartz F).comp (slice (infPartPi (K := F) 0))), fun f => ?_⟩
  rw [lD_apply (Submodule.subset_span ⟨f, g, hg, rfl⟩), show pureA F f g = schwartzBruhatTensorPi f g from rfl,
    sl_tensor, adelicFourierPi_schwartzBruhatTensorPi]
  exact mul_comm _ _

theorem std_eq (h : IsStd ψ) : ∃ ξ : F, ξ ≠ 0 ∧ ∀ x, ψ x = (adelicChar F (algebraMap F (AF F) ξ * x) : ℂ) := by
  obtain ⟨ξ, e⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ h.1 h.2.1
  obtain ⟨x, hx⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one h
  exact ⟨ξ, fun h0 => hx (by simp [e, h0]), e⟩

theorem elim_dot (a a' b b' : κ → AF F) : Sum.elim a a' ⬝ᵥ Sum.elim b b' = a ⬝ᵥ b + a' ⬝ᵥ b' := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem lD_schr (h : IsStd ψ) {ξ : F} (e : ∀ x, ψ x = (adelicChar F (algebraMap F (AF F) ξ * x) : ℂ))
    (hΦ : Φ ∈ schA F (κ ⊕ κ)) (a a' b b' : κ → AF F) :
    lD F κ (schr ψ (Sum.elim a a', Sum.elim b b') Φ) = ψ (⅟(2 : AF F) * (a ⬝ᵥ b + a' ⬝ᵥ b') - a' ⬝ᵥ (b + b')) *
      adelicFourierPi F (sl (a - a') Φ) (algebraMap F (AF F) ξ • (b + b')) := by
  rw [lD_int (GlobalTheory.HeisSchA.schr_mem_schA ψ h _ Φ hΦ), adelicFourierPi, ← integral_const_mul, eq_comm,
    ← integral_add_right_eq_self _ a', eq_comm]
  refine integral_congr_ae (.of_forall fun u => ?_)
  have : ∑ i, (u + a') i * (algebraMap F (AF F) ξ • (b + b')) i = algebraMap F (AF F) ξ * ((u + a') ⬝ᵥ (b + b')) := by
    rw [← smul_eq_mul, ← dotProduct_smul]; rfl
  simp only [schr, sl]
  rw [this, ← e, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]
  congr 2
  · funext i; cases i <;> simp
  · simp only [elim_dot, add_dotProduct, dotProduct_add]; ring

theorem lD_kill (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ)) (a b : κ → AF F) :
    lD F κ (schr ψ (Sum.elim a a, Sum.elim b (-b)) Φ) = lD F κ Φ := by
  obtain ⟨ξ, -, e⟩ := std_eq h
  rw [lD_schr h e hΦ, lD_apply hΦ]; simp

theorem lD_inj (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ))
    (h0 : ∀ a b, lD F κ (schr ψ (Sum.elim a 0, Sum.elim b 0) Φ) = 0) : Φ = 0 := by
  obtain ⟨ξ, hξ, e⟩ := std_eq h
  have k : ∀ a, adelicFourierPi F (sl a Φ) = 0 := fun a => funext fun b => by
    have := h0 a (algebraMap F (AF F) ξ⁻¹ • b)
    rw [lD_schr h e hΦ, sub_zero, add_zero, smul_smul, ← map_mul, mul_inv_cancel₀ hξ, map_one, one_smul] at this
    exact (mul_eq_zero.1 this).resolve_left (by rw [e]; exact Circle.coe_ne_zero _)
  funext z
  have := congrFun (adelicFourierPi_adelicFourierPi ((sl_mem hΦ).1 (z ∘ .inl - z ∘ .inr))) (-(z ∘ .inr))
  rw [k, adelicFourierPi_zero] at this
  simpa [sl] using this.symm

theorem lD_theta (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    HasSum (fun p : (κ → F) × (κ → F) => lD F κ (schr ψ (Sum.elim (rt p.1) (-rt p.1), Sum.elim (rt p.2) (rt p.2)) Φ))
      (thetaSum F Φ) := by
  obtain ⟨ξ, hξ, e⟩ := std_eq h
  have h2 : ξ * 2 ≠ 0 := mul_ne_zero hξ two_ne_zero
  convert ((Equiv.smulRight (β := κ → F) (two_ne_zero (α := F))).prodCongr (Equiv.smulRight (β := κ → F) h2)).hasSum_iff.2
    (hasSum_sl hΦ) using 2 with p
  have : ⅟(2 : AF F) * (rt p.1 ⬝ᵥ rt p.2 + -rt p.1 ⬝ᵥ rt p.2) - -rt p.1 ⬝ᵥ (rt p.2 + rt p.2) =
      algebraMap F (AF F) (p.1 ⬝ᵥ (p.2 + p.2)) := by
    simp [dotProduct]
  rw [lD_schr h e hΦ, this, h.2.1, one_mul]
  congr 2 <;> funext i <;> simp [rt, map_ofNat] <;> ring

theorem star_mem {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : star φ ∈ schA F κ :=
  (GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star F κ φ).2 h

theorem box_mem {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) : boxFun φ (star φ') ∈ schA F (κ ⊕ κ) :=
  GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ h _ (star_mem h')

theorem theta_box {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) :
    thetaSum F (boxFun φ (star φ')) = thetaSum F φ * star (thetaSum F φ') := by
  rw [show star (thetaSum F φ') = _ from (GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star F κ φ').1.symm, thetaSum, thetaSum,
    thetaSum, tsum_mul_tsum_of_summable_norm (summable_norm_of_mem_schA F h) (summable_norm_of_mem_schA F (star_mem h')),
    ← (Equiv.sumArrowEquivProdArrow κ κ F).tsum_eq]
  rfl

theorem borel_eq : (MeasurableSpace.pi : MeasurableSpace (κ → AF F)) = borel _ := BorelSpace.measurable_eq

theorem lD_haar (ν : @Measure (κ → AF F) (borel _)) (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, lD F κ (boxFun φ (star φ')) = c * ∫ u, φ u * star (φ' u) ∂ν := by
  revert ν
  rw [← borel_eq]
  intro ν hν
  refine ⟨Measure.addHaarScalarFactor (adeleMeasurePi F) ν, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    fun φ h φ' h' => ?_⟩
  rw [lD_int (box_mem h h')]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (adeleMeasurePi F) ν, integral_smul_nnreal_measure]
  rfl

theorem lD_sq {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) :
    lD F κ (boxFun φ (star φ)) = (∫⁻ x, ‖φ x‖ₑ ^ 2 ∂adeleMeasurePi F).toReal := by
  rw [lD_int (box_mem h h)]
  have : ∀ u, boxFun φ (star φ) (Sum.elim u u) = ((‖φ u‖ ^ 2 : ℝ) : ℂ) := fun u => by
    simp [boxFun, Complex.mul_conj']
  simp only [this]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ => sq_nonneg _)
    ((continuous_of_mem_schwartzBruhatPi h).norm.pow 2).aestronglyMeasurable]
  simp [ENNReal.ofReal_pow, ofReal_norm_eq_enorm]

theorem lD_unit {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hu : IsUnitaryOn (adeleClass F) om)
    (hp : ∀ g, ∀ φ ∈ schA F κ, om g φ ∈ schA F κ) (g : G) {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) :
    lD F κ (boxFun (om g φ) (star (om g φ'))) = lD F κ (boxFun φ (star φ')) := by
  have k : ∀ φ ∈ schA F κ, lD F κ (boxFun (om g φ) (star (om g φ))) = lD F κ (boxFun φ (star φ)) := fun φ h => by
    unfold IsUnitaryOn at hu
    rw [← borel_eq] at hu
    rw [lD_sq h, lD_sq (hp g φ h), hu _ inferInstance g φ h]
  have k1 := k _ (add_mem h h')
  have k2 := k _ (add_mem h (Submodule.smul_mem _ Complex.I h'))
  simp only [map_add, map_smul, star_add, star_smul, GlobalTheory.SchwartzBox.boxFun_add_left, GlobalTheory.SchwartzBox.boxFun_add_right,
    GlobalTheory.SchwartzBox.boxFun_smul_left, GlobalTheory.SchwartzBox.boxFun_smul_right, k φ h, k φ' h', smul_eq_mul,
    Complex.star_def, Complex.conj_I] at k1 k2
  linear_combination (1 / 2) * k1 + (Complex.I / 2) * k2 + (1 / 2 * (lD F κ (boxFun (om g φ) (star (om g φ'))) -
    lD F κ (boxFun φ (star φ')) - lD F κ (boxFun (om g φ') (star (om g φ))) + lD F κ (boxFun φ' (star φ)))) * Complex.I_mul_I

end GlobalTheory.ThK.Dbl

end
end

