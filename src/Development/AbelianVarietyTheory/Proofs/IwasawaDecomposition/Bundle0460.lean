import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InModIffForallPlaceMemSpanModulo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc.Crt

theorem mem_sup_prod_smul {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] (T N : Submodule R M)
    (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) {y : M} (hy : y ∈ N) (s : Finset ι)
    (h : ∀ i ∈ s, y ∈ T ⊔ I i • N) : y ∈ T ⊔ (∏ i ∈ s, I i) • N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.mem_sup_right hy
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hc : IsCoprime (I i) (∏ j ∈ s, I j) :=
      IsCoprime.prod_right fun j hj => hI i j (fun e => hi (e ▸ hj))
    obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hc
    have key : ∀ (A B : Ideal R) (c : R), c ∈ A → y ∈ T ⊔ B • N → c • y ∈ T ⊔ (A * B) • N := by
      intro A B c hc hy
      obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine Submodule.add_mem_sup (T.smul_mem c ht) ?_
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hc hz
    have e : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine Submodule.add_mem _ (key _ _ a ha h2) ?_
    rw [mul_comm]
    exact key _ _ b hb h1

theorem mem_sup_smul_mono {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {T N : Submodule R M}
    {I J : Ideal R} (h : I ≤ J) {y : M} (hy : y ∈ T ⊔ I • N) : y ∈ T ⊔ J • N :=
  (sup_le_sup_left (Submodule.smul_mono_left h) T : T ⊔ I • N ≤ T ⊔ J • N) hy

theorem prod_le_span {O : Type*} [CommRing O] [IsDedekindDomain O] {g : O} (hg : g ≠ 0)
    (hsq : ∀ w : HeightOneSpectrum O, g ∉ w.asIdeal ^ 2) (s : Finset (HeightOneSpectrum O))
    (hs : ∀ w : HeightOneSpectrum O, g ∈ w.asIdeal → w ∈ s) :
    ∏ w ∈ s, w.asIdeal ≤ Ideal.span {g} := by
  have h0 : (Ideal.span {g} : Ideal O) ≠ ⊥ := fun e => hg (Ideal.span_singleton_eq_bot.1 e)
  have hsf : Squarefree (Ideal.span {g} : Ideal O) := by
    refine (squarefree_iff_no_irreducibles (x := (Ideal.span {g} : Ideal O)) h0).2 ?_
    intro x hx hd
    have hp : Prime x := UniqueFactorizationMonoid.irreducible_iff_prime.1 hx
    refine hsq ⟨x, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ ?_
    rw [Ideal.dvd_span_singleton, ← pow_two] at hd
    exact hd
  have hrad : (Ideal.span {g}).radical ≤ Ideal.span {g} := by
    rintro x ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsf.isRadical n _ hn
  refine le_trans ?_ hrad
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP1, hP2⟩
  have hP0 : P ≠ ⊥ := fun e => h0 (le_bot_iff.1 (hP1.trans e.le))
  have hm := hs ⟨P, hP2, hP0⟩ ((Ideal.span_singleton_le_iff_mem _).1 hP1)
  have hle : ∏ w ∈ s, w.asIdeal ≤ (⟨P, hP2, hP0⟩ : HeightOneSpectrum O).asIdeal :=
    (Ideal.prod_le_inf (s := s) (f := fun w : HeightOneSpectrum O => w.asIdeal)).trans (Finset.inf_le hm)
  exact hle

variable {D : D7}

theorem g_not_mem_sq (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := by
  intro hm
  have hc : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have key : ∀ k (b : 𝓞 D.host.E), IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) b →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) * b ∈ w.asIdeal ^ 2 → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    rintro k b ⟨u, v, huv⟩ h hk
    refine (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.1 ?_
    have e : ((D.host.g k : ℕ) : 𝓞 D.host.E) =
        u * ((D.host.g k : ℕ) : 𝓞 D.host.E) ^ 2 + v * (((D.host.g k : ℕ) : 𝓞 D.host.E) * b) := by
      linear_combination (-((D.host.g k : ℕ) : 𝓞 D.host.E)) * huv
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hk 2)) (Ideal.mul_mem_left _ _ h)
  rw [Nat.cast_mul] at hm
  rcases w.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero hm) with h | h
  · exact key 0 _ hc hm h
  · exact key 1 _ hc.symm (mul_comm (G := 𝓞 D.host.E) _ _ ▸ hm) h

def toInt (I : Formalism.MainNotions.S.AutInst) : 𝓞 I.E →+* Formalism.MainNotions.S.IntAf I.F I.E :=
  ((Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).comp (algebraMap (𝓞 I.E) I.E)).codRestrict _ fun t =>
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 I.E) I.E t, ⟨t, rfl⟩⟩, rfl⟩)

theorem toInt_smul (I : Formalism.MainNotions.S.AutInst) (a : 𝓞 I.E) (y : Fin I.n → I.E) :
    toInt I a • incl I y = incl I ((a : I.E) • y) := by
  funext i
  show Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (a : I.E) * Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i) =
    Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((a : I.E) * y i)
  rw [map_mul]

def hostInt (X : HidaSetting D) : 𝓞 D.host.E →+* Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  (toInt X.B.I).comp (RingOfIntegers.mapRingEquiv X.ιE.symm).toRingHom

theorem wLf_eq (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    wLf X w = (w.asIdeal.map (hostInt X)) • X.B.I.Lf := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    show incl X.B.I x ∈ (w.asIdeal.map (hostInt X)) • X.B.I.Lf
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ⟨b, hb, hab⟩, y, hy, rfl⟩ := hz
      rw [← toInt_smul]
      have : toInt X.B.I a = hostInt X b := by
        refine congrArg (toInt X.B.I) (RingOfIntegers.ext ?_)
        show (a : X.B.I.E) = X.ιE.symm (b : D.host.E)
        rw [← hab, RingEquiv.symm_apply_apply]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hb) (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    | zero =>
      have : incl X.B.I 0 = 0 := funext fun i => map_zero _
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : incl X.B.I (x + y) = incl X.B.I x + incl X.B.I y := funext fun i => map_add _ _ _
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : incl X.B.I (a • x) = toInt X.B.I a • incl X.B.I x := (toInt_smul _ a x).symm
      rw [this]; exact Submodule.smul_mem _ _ hx
  · unfold Ideal.map
    rw [show X.B.I.Lf = Submodule.span _ (Set.range fun x : X.B.I.L => incl X.B.I x) from rfl]
    rw [Submodule.span_smul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, _, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    show toInt X.B.I (RingOfIntegers.mapRingEquiv X.ιE.symm b) • incl X.B.I y ∈ wLf X w
    rw [toInt_smul]
    refine Submodule.subset_span ⟨⟨_, Submodule.subset_span ⟨_, ⟨b, hb, ?_⟩, y, hy, rfl⟩⟩, rfl⟩
    exact X.ιE.apply_symm_apply _

theorem mL_eq (X : HidaSetting D) (m : ℕ) :
    mL X.B.I m = ((Ideal.span {(m : 𝓞 D.host.E)}).map (hostInt X)) • X.B.I.Lf := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_smul (r := (m : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)) (Ideal.mem_span_singleton_self _) hx
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)

theorem inMod_iff_forall_modW : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (S : Set (VA X.B.I)), S ⊆ X.B.I.Lf → ∀ y ∈ X.B.I.Lf, (InMod X.B.I X.B.g S y ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.GroupLoc.ModW X w S y) := by
  intro D X _ _ S _ y hy
  unfold InMod ModW
  simp only [mL_eq, wLf_eq]
  constructor
  · intro h w hw
    exact mem_sup_smul_mono (Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).2 hw)) h
  · intro h
    have hg : ((X.B.g : ℕ) : 𝓞 D.host.E) ≠ 0 := by
      rw [X.g_eq]
      exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hfin : {w : HeightOneSpectrum (𝓞 D.host.E) | ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal}.Finite := by
      have := Ideal.finite_factors (I := Ideal.span {((X.B.g : ℕ) : 𝓞 D.host.E)}) (by simpa using hg)
      simpa only [Ideal.dvd_span_singleton] using this
    have h1 := mem_sup_prod_smul _ _ (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.asIdeal.map (hostInt X))
      (fun i j hij => by
        rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup,
          i.isMaximal.coprime_of_ne j.isMaximal (fun e => hij (HeightOneSpectrum.ext e)), Ideal.map_top])
      hy hfin.toFinset (fun w hw => h w (hfin.mem_toFinset.1 hw))
    refine mem_sup_smul_mono ?_ h1
    have h2 := prod_le_span hg (fun w => by rw [X.g_eq]; exact g_not_mem_sq w) hfin.toFinset
      (fun w hw => hfin.mem_toFinset.2 hw)
    refine le_trans (le_of_eq ?_) (Ideal.map_mono h2)
    exact (map_prod (Ideal.mapHom (hostInt X)) _ _).symm

end GlobalTheory.Mem.GroupLoc.Crt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerNormOneFiniteAdeleDetClassStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | exact GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | (intros; apply GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtInProd

section Cut

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def cutMat (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem cutMat_one (e : R) : cutMat e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [cutMat, ← add_smul, add_sub_cancel, one_smul]

theorem cutMat_one_left (M : Matrix (Fin n) (Fin n) R) : cutMat 1 M = M := by
  rw [cutMat, one_smul, sub_self, zero_smul, add_zero]

theorem cutMat_zero_left (M : Matrix (Fin n) (Fin n) R) : cutMat 0 M = 1 := by
  rw [cutMat, zero_smul, sub_zero, one_smul, zero_add]

theorem cutMat_mul {e : R} (he : e * e = e) (M N : Matrix (Fin n) (Fin n) R) :
    cutMat e (M * N) = cutMat e M * cutMat e N := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1,
    h2, h3, zero_smul, add_zero, zero_add]

theorem cutMat_mul_compl {e : R} (he : e * e = e) (M : Matrix (Fin n) (Fin n) R) :
    cutMat e M * cutMat (1 - e) M = M := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem map_cutMat (f : R →+* S) (e : R) (M : Matrix (Fin n) (Fin n) R) :
    (cutMat e M).map f = cutMat (f e) (M.map f) := by
  ext i j
  by_cases h : i = j <;> simp [cutMat, Matrix.one_apply, h]

theorem conjT_cutMat (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    ReciprocityTheory.Aut.conjT σ (cutMat e M) = cutMat e (ReciprocityTheory.Aut.conjT σ M) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ReciprocityTheory.Aut.conjT, cutMat, hσ]
  · simp [ReciprocityTheory.Aut.conjT, cutMat, hσ, Matrix.one_apply, h, Ne.symm h]

def cutHom {e : R} (he : e * e = e) : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R where
  toFun := cutMat e
  map_one' := cutMat_one e
  map_mul' := cutMat_mul he

end Cut

section Adelic

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open Classical

def idemF (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AFplus L :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem idemF_apply (v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (idemF (L := L) v) w = if w = v then 1 else 0 := rfl

theorem idemF_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemF (L := L) v * idemF v = idemF v := by
  apply Subtype.ext
  funext w
  show (if w = v then (1 : w.adicCompletion (maximalRealSubfield L)) else 0) * (if w = v then 1 else 0) = (if w = v then 1 else 0)
  split_ifs <;> simp

variable (L) in

def eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] idemF v

theorem eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v * eA L v = eA L v := by
  rw [eA, Algebra.TensorProduct.tmul_mul_tmul, one_mul, idemF_mul]

theorem conj_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : conjAL L (eA L v) = eA L v := by
  simp [conjAL, eA, Algebra.TensorProduct.map_tmul]

theorem compAt_eA (w v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L w (eA L v) = if w = v then 1 else 0 := by
  have : compAt L w (eA L v) = (1 : L) ⊗ₜ[maximalRealSubfield L] ((idemF (L := L) v) w) := rfl
  rw [this, idemF_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem eA_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v ∈ ALint L :=
  Subring.subset_closure (Or.inr ⟨idemF v, fun w => by
    rw [idemF_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _, rfl⟩)

def cutGA {e : AL L} (he : e * e = e) (hc : conjAL L e = e) : GA L n →* GA L n :=
  ((Units.map (cutHom (n := n) he)).comp (GA L n).subtype).codRestrict _ (fun g => by
    have hg : (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) g.1 = 1 := g.2
    show cutMat e (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (cutMat e g.1) = 1
    rw [conjT_cutMat _ hc, ← cutMat_mul he, hg, cutMat_one])

theorem cutGA_val {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) = cutMat e g.1 := rfl

theorem cutGA_mem_Umax {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (heI : e ∈ ALint L) {g : GA L n}
    (hg : g ∈ Umax L n) : cutGA he hc g ∈ Umax L n := by
  have hg' : ∀ i j, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := hg
  show ∀ i j, ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
  intro i j
  rw [cutGA_val]
  simp only [cutMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  refine Subring.add_mem _ (Subring.mul_mem _ heI (hg' i j)) (Subring.mul_mem _ (Subring.sub_mem _ (Subring.one_mem _) heI) ?_)
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

end Adelic

section Adelic2

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cut_map_compAt {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) =
      cutMat (compAt L w e) ((g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w)) := by
  rw [cutGA_val, map_cutMat]

theorem one_sub_eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (1 - eA L v) * (1 - eA L v) = 1 - eA L v := by
  rw [mul_sub, mul_one, sub_mul, one_mul, eA_mul, sub_self, sub_zero]

theorem conj_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (1 - eA L v) = 1 - eA L v := by
  rw [map_sub, map_one, conj_eA]

theorem triv_cut_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v} (cutGA (eA_mul v) (conj_eA v) g) := by
  intro w hw
  rw [cut_map_compAt, compAt_eA, if_neg (fun h => hw (Set.mem_singleton_iff.2 h)), cutMat_zero_left]

theorem triv_cut_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v}ᶜ (cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g) := by
  intro w hw
  have hwv : w = v := by simpa using hw
  rw [cut_map_compAt, map_sub, map_one, compAt_eA, if_pos hwv, sub_self, cutMat_zero_left]

theorem cut_eA_at (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    ((cutGA (eA_mul v) (conj_eA v) g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  rw [cut_map_compAt, compAt_eA, if_pos rfl, cutMat_one_left]

theorem cut_mul_cut (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    cutGA (eA_mul v) (conj_eA v) g * cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g = g :=
  Subtype.ext (Units.ext (cutMat_mul_compl (eA_mul v) _))

end Adelic2

theorem main : ∀ (D : D7) (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), NG.IsProdLevel (stdJ (datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi)) := by
  intro D n hr Pg Q ψ chi xi κ hκ v
  obtain ⟨hUA, hSt, hred, -⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D n
  set κ1 := cutGA (eA_mul v) (conj_eA v) κ with hκ1
  set κ2 := cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) κ with hκ2
  have hκ' := Subgroup.mem_comap.1 hκ
  rw [mem_lev, mem_parLev] at hκ'
  obtain ⟨⟨-, hSκ, hPg, hQ⟩, hT⟩ := hκ'
  have hUm : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hSt κ).1 hSκ
  have hUm1 : κ1 ∈ ReciprocityTheory.Aut.Umax D.host.E n := cutGA_mem_Umax _ _ (eA_mem v) hUm
  have hUm2 : κ2 ∈ ReciprocityTheory.Aut.Umax D.host.E n :=
    cutGA_mem_Umax _ _ (Subring.sub_mem _ (Subring.one_mem _) (eA_mem v)) hUm
  have key : ∀ PP, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) ∨
      redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = 1 := by
    intro PP
    have hov : NG.OverPl PP (underPl (maximalRealSubfield D.host.E) PP) := (underPl_asIdeal (F := maximalRealSubfield D.host.E) PP).symm
    by_cases h : underPl (maximalRealSubfield D.host.E) PP = v
    · left
      rw [← cut_mul_cut v κ, map_mul, redFn_mul ((hSt _).2 hUm1) ((hSt _).2 hUm2),
        hred κ2 hUm2 {v}ᶜ _ PP (triv_cut_one_sub_eA v κ) (h ▸ hov) (by simp), mul_one]
    · right
      exact hred κ1 hUm1 {v} _ PP (triv_cut_eA v κ) hov h
  refine ⟨κ1, ?_, triv_cut_eA v κ, cut_eA_at v κ⟩
  apply Subgroup.mem_comap.2
  rw [mem_lev, mem_parLev]
  refine ⟨⟨hUA κ1, (hSt κ1).2 hUm1, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rcases key PP with h | h <;> rw [h]
    · exact hPg PP hP
    · exact Subgroup.one_mem _
  · rcases key PP with h | h <;> rw [h]
    · exact hQ PP hP
    · exact Subgroup.one_mem _
  · intro PP _
    have hT' := hT PP (Set.mem_univ _)
    show upperLeftBlock _ (redFn _ PP.1 (km D n κ1)) ∈ _
    rcases key PP.1 with h | h <;> rw [h]
    · exact hT'
    · have h2 : upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
      show upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) ∈ unip (kP PP.1) D.R.r
      rw [h2]
      exact (unip (kP PP.1) D.R.r).one_mem

end GlobalTheory.MtInProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTupleGroupClassesCoordinatesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_tuple_group_classes_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG B.host.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG B.host.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG B.host.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  first | exact @GlobalTheory.stpTop_groupClasses | exact GlobalTheory.stpTop_groupClasses | (intros; apply GlobalTheory.stpTop_groupClasses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTwistLevelContainsPrincipalCongruenceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_twist_level_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  first | exact @GlobalTheory.Mem.Col2.TC.levQ_top_princ | exact GlobalTheory.Mem.Col2.TC.levQ_top_princ | (intros; apply GlobalTheory.Mem.Col2.TC.levQ_top_princ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPasses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem untw_set_eq (B : Base) (pl : Finset ℕ) (f : Fr B.toPre) :
    (TwDat.untw B pl).set f = {1, f.del, f.del'} := by
  refine Set.union_eq_left.2 ?_
  rintro _ ⟨w, rfl⟩
  change (if _ then f.del' else f.del) * 1 ∈ _
  rw [mul_one]
  split_ifs
  · exact .inr (.inr rfl)
  · exact .inr (.inl rfl)

theorem recAtG_of_two_passes : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  intro h2v KP Q Q' hK hF hX hS
  have hL := EvG.imp (EvG.inter hF (EvG.inter hX hS)) fun K _ _ _ _ H =>
    (large₂.inter (large₂.inter H.1 (lg_forced K)) (large₂.inter H.2.1 H.2.2))
  refine EvG.imp (EvG.inter (EvG.inter hK.ex hL) (evG_of_ev GlobalTheory.Mem.Top.LayOfCore.lay_of_core)) ?_
  rintro K _ _ _ _ ⟨⟨⟨P, f₀, hO, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩, hlay⟩
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks (S₁ P f₀) (fun F F₀ => S₂ P f₀ F F₀ {1, f₀.del, f₀.del'}) (a₁ _ _)
    (fun F F₀ => a₂ _ _ F F₀ _)
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨⟨h1, hfo⟩, h2, h3⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hO
    ⟨hH₁, by rw [untw_set_eq]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _))
  obtain ⟨C, W, V, S, N, G, c, hQ⟩ := h1 hKP hfo rfl
  obtain ⟨B', f', T', -, -, -, -, -, C', W', V', S', N', G', c', -, hTw, hQ'⟩ :=
    h3 hKP rfl C W V S N G c hQ (h2 hKP rfl C W V S N G c hQ) (fun _ => ∅) (fun _ _ _ => ∅) (by simp)
  obtain ⟨Y, hY, k1, k2, k3, k4⟩ := hlay ⟨B', C', W', V', S', N', G'⟩ f' T' c' (h2v _ c'.real.vol)
  have hTw' : DQ.TwAllAt (Stages.toD7 ⟨B', C', W', V', S', N', G'⟩) Y.nch Y.xd := by
    have e1 : Y.nch = c'.O.nch := by rw [← hY]; rfl
    have e2 : Y.xd = c'.O.xd := by rw [← hY]; rfl
    rw [e1, e2]
    exact hTw
  exact ⟨_, Y, k1, k2, k3, hTw'.twAt, ⟨_, f', T', c', hQ', by rw [hY]⟩, k4, hTw', c'.mtStable⟩

example : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) → ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' → RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := recAtG_of_two_passes

end GlobalTheory.Mem.Top.GroupRetwisting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterAtQFiniteOrderAndTrivialStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacterAtQ_finite_order_and_trivial : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1), ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧ ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.topChi_finite_order_and_trivial | exact GlobalTheory.Mem.Col2.TopCh.topChi_finite_order_and_trivial | (intros; apply GlobalTheory.Mem.Col2.TopCh.topChi_finite_order_and_trivial <;> assumption)
end

