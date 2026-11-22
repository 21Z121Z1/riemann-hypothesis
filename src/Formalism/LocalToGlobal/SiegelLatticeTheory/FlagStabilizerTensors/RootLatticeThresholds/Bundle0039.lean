import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRedKer

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.MainNotions.BridgeLemma

variable {D : D7}

def sigH (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

theorem sigH_coe (a : 𝓞 D.host.E) : ((sigH D a : 𝓞 D.host.E) : D.host.E) = D.host.conj (a : D.host.E) := rfl

def conjH (w : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (sigH D)
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (sigH D).surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

theorem conj_conj (X : HidaSetting D) (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  obtain ⟨x, rfl⟩ := X.ιE.surjective y
  rw [← X.ιE_conj, ← X.ιE_conj, star_star]

theorem sigH_sigH (X : HidaSetting D) (a : 𝓞 D.host.E) : sigH D (sigH D a) = a := by
  apply RingOfIntegers.ext
  rw [sigH_coe, sigH_coe]
  exact conj_conj X _

theorem conjH_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : conjH (conjH w) = w := by
  apply HeightOneSpectrum.ext
  show (w.asIdeal.comap (sigH D)).comap (sigH D) = w.asIdeal
  ext a
  simp only [Ideal.mem_comap]
  rw [sigH_sigH X]

theorem isConjPl_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : IsConjPl D.host w (conjH w) := by
  intro x y hxy
  have hs : sigH D y = x := by
    apply RingOfIntegers.ext
    rw [sigH_coe, hxy, conj_conj X]
  show x ∈ w.asIdeal ↔ sigH D y ∈ w.asIdeal
  rw [hs]

theorem natCast_mem_conjH {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ} (h : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    (p : 𝓞 D.host.E) ∈ (conjH w).asIdeal := by
  show sigH D (p : 𝓞 D.host.E) ∈ w.asIdeal
  rw [map_natCast]
  exact h

theorem wB_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : wB X (conjH w) = wc X.B.I (wB X w) := by
  apply HeightOneSpectrum.ext
  ext a
  rw [mem_wc]
  simp only [wB, conjH, Ideal.mem_comap]
  have hc : sigH D (RingOfIntegers.mapRingEquiv X.ιE a) =
      RingOfIntegers.mapRingEquiv X.ιE (sigO X.B.I a) := by
    apply RingOfIntegers.ext
    rw [sigH_coe]
    simp [RingOfIntegers.mapRingEquiv, sigO_coe, X.ιE_conj]
  rw [hc]

theorem finrank_cmField (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv, Formalism.HC.Frame.natCard_GG]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

theorem cover (X : HidaSetting D) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = conjH (D.naut.plGw k v) := by
  have hp := D.host.g_prime k
  set A : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
    Set.range (D.naut.plGw k) ∪ Set.range (fun v => conjH (D.naut.plGw k v)) with hA
  set T : Set (HeightOneSpectrum (𝓞 D.host.E)) := placesOver D.host.E (D.host.g k) with hT
  have hAT : A ⊆ T := by
    rintro _ (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact D.naut.plGw_over k v
    · exact natCast_mem_conjH (D.naut.plGw_over k v)
  have hTfin : T.Finite := finite_plOver D.host.E hp
  have hinj2 : Function.Injective (fun v => conjH (D.naut.plGw k v)) := by
    intro v v' h
    apply D.naut.plGw_inj k
    have := congrArg conjH h
    simpa only [conjH_conjH X] using this
  have hdisj : Disjoint (Set.range (D.naut.plGw k)) (Set.range (fun v => conjH (D.naut.plGw k v))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨v', hv'⟩
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    have hv'' : conjH (D.naut.plGw k v') = D.naut.plGw k v := hv'
    rw [hv''] at this
    exact this
  have hcA : A.ncard = 2 * D.R.f := by
    rw [hA, Set.ncard_union_eq hdisj (Set.finite_range _) (Set.finite_range _),
      Set.ncard_range_of_injective (D.naut.plGw_inj k), Set.ncard_range_of_injective hinj2,
      Nat.card_eq_fintype_card, D.nd.card_PlG k]
    ring
  have hcT : T.ncard = 2 * D.R.f := by rw [hT, D.nd.g_split k, finrank_cmField]
  have hEq : A = T := Set.eq_of_subset_of_ncard_le hAT (by rw [hcA, hcT]) hTfin
  have : w ∈ A := by rw [hEq]; exact hw
  rcases this with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨v, Or.inl rfl⟩
  · exact ⟨v, Or.inr rfl⟩

theorem unram (X : HidaSetting D) (k : Fin 2) (P : Ideal (𝓞 X.B.I.E)) (hPm : P.IsMaximal)
    (hgP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have hQm : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
    have := Ideal.mem_map_of_mem e hgP
    rwa [map_natCast] at this
  obtain ⟨-, hsq⟩ := hspl _ hQm hgQ
  intro h
  apply hsq
  have := Ideal.mem_map_of_mem e h
  rwa [map_natCast, Ideal.map_pow] at this

def toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv X.ιE).symm
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv X.ιE).symm.surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

theorem wB_toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : wB X (toH X w) = w := by
  apply HeightOneSpectrum.ext
  ext a
  simp [wB, toH, Ideal.mem_comap]

theorem redKerP_holds (X : HidaSetting D) (k : Fin 2) : Formalism.L2.SG.AllRowsOf.RedKerP X k := by
  intro x hx hred
  have hp := D.host.g_prime k
  have hA : ∀ v, ∀ y ∈ X.B.I.Lf, (X.B.I.fmat x - 1) *ᵥ y ∈ Lq X.B.I (wB X (D.naut.plGw k v)) := by
    intro v
    have h0 := (redMat_iff X _ _ x _).1 (hred v)
    exact stepA X.B.I hp (by rw [card_wB, card_res_host]) hx h0
  refine glue X.B.I hp (unram X k) hx fun w hw => ?_
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X w).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [map_natCast]; exact hw
  obtain ⟨v, hv | hv⟩ := cover X k (toH X w) hwH
  · rw [← wB_toH X w, hv]
    exact hA v
  · rw [← wB_toH X w, hv, wB_conjH X]
    exact stepB X.B.I hx (hA v)

end Formalism.L2.SG.Pf.AllRowsRedKer
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRho
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRho

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA

variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

def RedMatB (p : ℕ) {m : ℕ} (b : Fin m → Fin I.n → I.E) (x : I.Gf) (M : Matrix (Fin m) (Fin m) (ZMod p)) : Prop :=
  ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w

theorem redMat0_of {p m : ℕ} {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf}
    {M : Matrix (Fin m) (Fin m) (ZMod p)} (h : RedMatB I w p b x M) : RedMat0 I w p x M := ⟨b, hb, h⟩

theorem natSmul_Lq (k : ℕ) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lq I w) :
    (k : I.E ⊗[I.F] Af I.F) • z ∈ Lq I w := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hz k

theorem redMatB_exists {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} (hx : x ∈ I.Kset) :
    ∃ M : Matrix (Fin m) (Fin m) (ZMod p), RedMatB I w p b x M := by
  have : NeZero p := ⟨hp.ne_zero⟩
  choose c hc using fun i => coords I w hp hcard hb (K_mv I hx (DictLat.iv_mem I (hb.1 i)))
  refine ⟨Matrix.of fun j i => ((c i j : ℤ) : ZMod p), fun i => ?_⟩
  have h2 : ∑ j, ((((c i j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    exact sum_mem fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have := sub_mem (hc i) h2
  convert this using 1
  simp only [Matrix.of_apply]
  abel

theorem mkQ_natSmul (k : ℕ) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (Lq I w).mkQ ((k : I.E ⊗[I.F] Af I.F) • v) = ((k : ℤ)) • (Lq I w).mkQ v := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]

theorem redMatB_unique {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ} (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} {M M' : Matrix (Fin m) (Fin m) (ZMod p)}
    (h : RedMatB I w p b x M) (h' : RedMatB I w p b x M') : M = M' := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  ext j i
  have hdiff : ∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
      ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) ∈ Lq I w := by
    have := sub_mem (h i) (h' i)
    convert this using 1
    abel
  have hz : ∑ l, ((((M' l i).val : ℕ) : ℤ) - (((M l i).val : ℕ) : ℤ)) • (Lq I w).mkQ (iv I (b l)) = 0 := by
    have h0 : (Lq I w).mkQ (∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
        ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hdiff
    rw [map_sub, map_sum, map_sum] at h0
    simp only [mkQ_natSmul] at h0
    rw [← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => sub_smul _ _ _
  have hj := Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A I w p hp hcard hb _ hz j
  have hj' : ((M' j i).val : ZMod p) - ((M j i).val : ZMod p) = 0 := by exact_mod_cast hj
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_eq_zero] at hj'
  exact hj'.symm

theorem redMatB_mul {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : ∀ i, b i ∈ I.L) {x y : I.Gf} (hx : x ∈ I.Kset)
    {M N : Matrix (Fin m) (Fin m) (ZMod p)} (hM : RedMatB I w p b x M) (hN : RedMatB I w p b y N) :
    RedMatB I w p b (x * y) (M * N) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro i
  have hAB : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
  have s1 : I.fmat x *ᵥ (I.fmat y *ᵥ iv I (b i)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) ∈ Lq I w := by
    have := stab_w I w hx (hN i)
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum] at this
    simpa only [Matrix.mulVec_smul] using this
  have s2 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun k _ => ?_
    rw [← smul_sub]
    exact natSmul_Lq I w _ (hM k)
  have e3 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_natCast, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_mul, mul_comm]
  have s3 : ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, ((((M * N) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    have hc : (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : ZMod p) = (M * N) j i := by
      rw [Int.cast_natCast, Nat.cast_sum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have := val_sub I w hp hcard (hb j) ((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ)
    rw [hc] at this
    have := neg_mem this
    rwa [neg_sub] at this
  rw [e3] at s2
  have := add_mem (add_mem s1 s2) s3
  rw [hAB, ← Matrix.mulVec_mulVec]
  convert this using 1
  abel

theorem redMatB_one {p : ℕ} (hp : p.Prime) {m : ℕ} (b : Fin m → Fin I.n → I.E) :
    RedMatB I w p b 1 (1 : Matrix (Fin m) (Fin m) (ZMod p)) := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  intro i
  have e : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      iv I (b i) := by
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
    · intro j _ hj; simp [Matrix.one_apply_ne hj]
    · simp
  rw [e, fmat_one, Matrix.one_mulVec, sub_self]
  exact zero_mem _

structure RedB (I : AutInst) (m : ℕ) where
  w : HeightOneSpectrum (𝓞 I.E)
  p : ℕ
  hp : p.Prime
  hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p
  hm : m = I.n
  b : Fin m → Fin I.n → I.E
  hb : IsRedBasis0 I w b

variable {I} {m : ℕ}

open Classical in

def matB (R : RedB I m) (x : I.Gf) : Matrix (Fin m) (Fin m) (ZMod R.p) :=
  if hx : x ∈ I.Kset then Classical.choose (redMatB_exists I R.w R.hp R.hcard R.hb hx) else 0

theorem matB_spec (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) : RedMatB I R.w R.p R.b x (matB R x) := by
  unfold matB; rw [dif_pos hx]; exact Classical.choose_spec (redMatB_exists I R.w R.hp R.hcard R.hb hx)

theorem matB_eq (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin m) (Fin m) (ZMod R.p)}
    (h : RedMatB I R.w R.p R.b x M) : matB R x = M :=
  redMatB_unique I R.w R.hp R.hcard R.hm R.hb (matB_spec R hx) h

theorem matB_mul (R : RedB I m) {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) :
    matB R (x * y) = matB R x * matB R y :=
  matB_eq R (K_mul I hx hy) (redMatB_mul I R.w R.hp R.hcard R.hb.1 hx (matB_spec R hx) (matB_spec R hy))

theorem matB_one (R : RedB I m) : matB R 1 = 1 := matB_eq R (K_one I) (redMatB_one I R.w R.hp R.b)

def rhoB (R : RedB I m) : Formalism.L2.SG.AllRowsOf.KSub I →* GL (Fin m) (ZMod R.p) :=
  MonoidHom.toHomUnits
    { toFun := fun x => matB R x
      map_one' := matB_one R
      map_mul' := fun x y => matB_mul R x.2 y.2 }

theorem rhoB_val (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) = matB R x := rfl

theorem rhoB_spec (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    RedMatB I R.w R.p R.b x ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) :=
  matB_spec R x.2

end Formalism.L2.SG.Pf.AllRowsRho
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PtParAnti
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

theorem ptPar_anti {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x y : ℕ), y < (bs.map Prod.snd).sum →
    x < y → blkOf bs x = blkOf bs y → ptPar bs y < ptPar bs x
  | [], _, y, hy, _, _ => by simp at hy
  | (t, s) :: bs, x, y, hy, hxy, h => by
    simp only [List.map_cons, List.sum_cons] at hy
    simp only [blkOf] at h
    rw [ptPar_cons, ptPar_cons]
    by_cases hys : y < s
    · rw [if_pos hys, if_pos (by omega)]; omega
    · by_cases hxs : x < s
      · rw [if_pos hxs, if_neg hys] at h; omega
      · rw [if_neg hxs, if_neg hys] at h ⊢
        have := ptPar_anti bs (x - s) (y - s) (by omega) (by omega) (by omega)
        omega

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hee_v (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.eX a) (X.eX b)
  rw [X.ee a b] at key
  simpa [HidaSetting.eR] using key

theorem hez_v (v : InfinitePlace X.B.I.F) (w : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.eX a) (X.zu w)
  rw [(X.zu_orth w a).1] at key
  simpa [HidaSetting.eR, HidaSetting.zR] using key

theorem hef_v (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.eX a) (X.fY b)
  rw [X.ef a b] at key
  split_ifs at key ⊢ <;> simpa [HidaSetting.eR, HidaSetting.fR] using key

theorem hfe_v (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if b = a then 1 else 0 := by
  rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_conj, hef_v X v b a]
  split_ifs <;> simp

theorem hfz_v (v : InfinitePlace X.B.I.F) (w : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR w)) = 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.fY a) (X.zu w)
  rw [(X.zu_orth w a).2] at key
  simpa [HidaSetting.fR, HidaSetting.zR] using key

theorem hJs_r {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJs_l {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) :
    hJ ε (c • x) y = starRingEnd ℂ c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul, starRingEnd_apply]

theorem gram_frm (v : InfinitePlace X.B.I.F) (w : D.what₂.Word) (sc : ℝ) (a b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (frm X w sc v a) (frm X w sc v b) = lastDiag (-((Tw w : ℝ) : ℂ)) a b := by
  have h0 : ∀ i j : Fin (D.R.rS + 1),
      hJ (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) i)
        (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) j) =
        lastDiag (-((Tw w : ℝ) : ℂ)) i j := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [fam, Fin.snoc_last, lastDiag, Matrix.of_apply]
        try simp only [and_self, ite_true, if_true]
        exact Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg (X := X) v w
      | cast j =>
        simp only [fam, Fin.snoc_last, Fin.snoc_castSucc, lastDiag, Matrix.of_apply]
        rw [if_neg (fun h => (Fin.castSucc_lt_last j).ne h.2), Formalism.L2.SG.PoincareInHH.Cut.hJ_conj,
          hez_v X v w j, map_zero]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [fam, Fin.snoc_last, Fin.snoc_castSucc, lastDiag, Matrix.of_apply]
        rw [if_neg (fun h => (Fin.castSucc_lt_last i).ne h.1), hez_v X v w i]
      | cast j =>
        simp only [fam, Fin.snoc_castSucc, lastDiag, Matrix.of_apply]
        rw [if_neg (fun h => (Fin.castSucc_lt_last i).ne h.1), hee_v X v i j]
  simp only [frm, famSc, hJs_l, hJs_r, h0]
  by_cases ha : a = Fin.last _
  · by_cases hb : b = Fin.last _
    · subst ha
      subst hb
      simp
    · simp [lastDiag, hb]
  · simp [lastDiag, ha]

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

