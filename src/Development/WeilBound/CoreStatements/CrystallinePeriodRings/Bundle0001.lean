import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

-- bundled from Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
section
noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem frob_root_eq {F : Type} [Field F] {a b : F} {m n : ℕ} (hm : 0 < m) (hc : m.Coprime n)
    (ha : a ^ m = 1) (hb : b ^ m = 1) (h : a ^ n = b ^ n) : a = b := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hb
    exact zero_ne_one hb
  have h1 : (a / b) ^ m = 1 := by rw [div_pow, ha, hb, div_one]
  have h2 : (a / b) ^ n = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ hb0)]
  have h3 : orderOf (a / b) = 1 :=
    Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  exact (div_eq_one_iff_eq hb0).1 (orderOf_eq_one_iff.1 h3)

theorem IsFrac.frob_injective {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {a t : A}
    (hf : IsFrac f a t) (hi : Function.Injective f) {F : B →+* B} {g : A →+* A}
    (hF : ∀ x, F (f x) = f (g x)) (hg : Function.Injective g) : Function.Injective F := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, n, y, h⟩ := hf.2.2 x
  have h1 := congrArg F h
  rw [map_mul, hx, mul_zero, hF] at h1
  have hy : y = 0 := hg (hi (by rw [← h1, map_zero, map_zero]))
  rw [hy, map_zero] at h
  exact ((hf.1.pow m).mul (hf.2.1.pow n)).mul_right_eq_zero.1 h

theorem frob_injective_of_fac {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E}
    {f : A →+* B} {g : A →+* E} (h : Fac F f g) (hg : Function.Injective g) :
    Function.Injective f := fun x y e => hg (by rw [← h, ← h, e])

theorem frob_fix_padic {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (F : B →+* B)
    (q : ℚ_[l] →+* B) (h : ∀ z : ℤ_[l], F (q (z : ℚ_[l])) = q (z : ℚ_[l])) (x : ℚ_[l]) :
    F (q x) = q x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := F.comp q) (k := q) (RingHom.ext h)) x

theorem frob_map_mul_natCast {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) (x : A) :
    f ((n : A) * x) = (n : B) * f x := by
  rw [map_mul, map_natCast]

theorem frob_not_mem_sq {R : Type} [CommRing R] [IsDomain R] {t : R} (ht : Irreducible t) :
    t ∉ Ideal.span {t} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h : t * (t * c) = t * 1 := by rw [mul_one, ← mul_assoc, ← sq, ← hc]
  exact ht.not_isUnit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ ht.ne_zero h))

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem frob_oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem frob_qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.cB l (algebraMap (AInf ℂ_[l] l)
    (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z)) := by
  apply ιCD_injective
  refine (ιCD_qB _).trans (Eq.trans ?_ (ιCD_cB _).symm)
  rw [cD_apply, ACris.iota_padicInt, frob_oD_apply, AlgHom.commutes]

theorem frob_phi_padicInt (z : ℤ_[l]) :
    ACris.phi ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
      (IsPerfectoidField.padicIntToWitt l z)) =
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z) := by
  rw [ACris.phi_algebraMap, ACris.frobenius_padicIntToWitt]

theorem φB_qB (q : ℚ_[l]) : Per6.φB l (qB l q) = qB l q :=
  frob_fix_padic (Per6.φB l) (qB l) (fun z =>
    (congrArg (Per6.φB l) (frob_qB_coe z)).trans (((φB_cB _).trans
      (congrArg (Per6.cB l) (frob_phi_padicInt z))).trans (frob_qB_coe z).symm)) q

theorem isUnit_tB : IsUnit (tB l) := (cB_isFrac l).2.1

theorem frob_phi_tA : ACris.phi ℂ_[l] l (Per6.tA l) = (l : ACris.ACris ℂ_[l] l) * Per6.tA l :=
  ACris.phi_periodT_eq_mul (untilt_epsilon (p := l))

theorem φB_tB : Per6.φB l (tB l) = (l : Per6.Bcris l) * tB l :=
  ((φB_cB (Per6.tA l)).trans (congrArg (Per6.cB l) frob_phi_tA)).trans
    (frob_map_mul_natCast (Per6.cB l) l (Per6.tA l))

theorem ιCD_tB : ιCD l (tB l) = algebraMap (Per6.BdRp l) (Per6.BdR l) (tBdR l) :=
  (ιCD_cB (Per6.tA l)).trans (cD_tA l)

theorem ιCD_tB_mem : ιCD l (tB l) ∈ Per6.FilD l 1 := by
  rw [ιCD_tB]
  refine (IsPerfectoidField.algebraMap_mem_fil_iff (K := ℂ_[l]) (p := l) (tBdR l) 1).2 ?_
  rw [pow_one, maximalIdeal_eq_span_tBdR]
  exact Ideal.mem_span_singleton_self _

theorem ιCD_tB_not_mem : ιCD l (tB l) ∉ Per6.FilD l 2 := by
  rw [ιCD_tB]
  intro h
  have h1 := (IsPerfectoidField.algebraMap_mem_fil_iff (K := ℂ_[l]) (p := l) (tBdR l) 2).1 h
  rw [maximalIdeal_eq_span_tBdR] at h1
  exact frob_not_mem_sq irreducible_tBdR h1

theorem frob_cB_injective : Function.Injective (Per6.cB l) :=
  frob_injective_of_fac (ιCD_fac l) (cD_injective l)

theorem φB_injective_of (h : Function.Injective (ACris.phi ℂ_[l] l)) :
    Function.Injective (Per6.φB l) :=
  (cB_isFrac l).frob_injective frob_cB_injective φB_cB h

theorem frob_aB_apply (a : Ainf l) : Per6.aB l a =
    Per6.cB l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) :=
  (RingHom.comp_apply _ _ a).trans (RingHom.comp_apply _ _ _)

theorem frob_coeff_tiltMap (xb : OCb l) (k : ℕ) (y : OC l)
    (h : PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    PreTilt.coeff k (Per6.tiltMap l xb) = Ideal.Quotient.mk _ (Per6.intEquiv l y) :=
  (show PreTilt.coeff k (Per6.tiltMap l xb) = Per6.modPEquiv l (PreTilt.coeff k xb) from rfl).trans
    ((congrArg (Per6.modPEquiv l) h).trans rfl)

theorem frob_tilt_root {c : ℂ_[l]} {m : ℕ} (hm : 0 < m) (hc : m.Coprime l)
    (x : PreTilt ↥(normInteger ℂ_[l]) l) (y : ℕ → ↥(normInteger ℂ_[l]))
    (h1 : ∀ k, (y k : ℂ_[l]) ^ (l ^ k) = c) (h2 : ∀ k, y k ^ m = 1)
    (h3 : ∀ k, PreTilt.coeff k x = Ideal.Quotient.mk _ (y k)) :
    x ^ m = 1 ∧ ((PreTilt.untilt x : ↥(normInteger ℂ_[l])) : ℂ_[l]) = c := by
  have h2' : ∀ k, (y k : ℂ_[l]) ^ m = 1 := fun k => by
    have := congrArg Subtype.val (h2 k)
    simpa using this
  have hy : ∀ n, y (n + 1) ^ l = y n := fun n => Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    refine frob_root_eq hm (hc.pow_right n) ?_ (h2' n) ?_
    · rw [← pow_mul, mul_comm, pow_mul, h2', one_pow]
    · rw [← pow_mul, ← pow_succ', h1, h1])
  have hx : x = IsPerfectoidField.ofCompatible l y hy := IsPerfectoidField.preTilt_ext l fun n => by
    rw [h3, IsPerfectoidField.coeff_ofCompatible]
  refine ⟨IsPerfectoidField.preTilt_ext l fun n => ?_, ?_⟩
  · rw [map_pow, h3, ← map_pow, h2, map_one, map_one]
  · rw [hx, IsPerfectoidField.untilt_ofCompatible, ← h1 0, pow_zero, pow_one]

theorem frob_iota_teich {ζ : PadicAlgCl l} {m : ℕ} (hm : 0 < m) (hζ : ζ ^ m = 1)
    (x : PreTilt ↥(normInteger ℂ_[l]) l) (hx : x ^ m = 1)
    (hu : ((PreTilt.untilt x : ↥(normInteger ℂ_[l])) : ℂ_[l]) = (ζ : ℂ_[l])) :
    ACris.iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
      (WittVector.teichmuller l x)) = algClToBdR l ζ := by
  have hζ0 : (ζ : ℂ_[l]) ≠ 0 := by
    intro h
    have := ACris.norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[l]) ^ m = 1 by
      rw [PadicComplex.coe_eq, ← map_pow, hζ, map_one])
    rw [h, norm_zero] at this
    exact zero_ne_one this
  apply ACris.eq_of_pow_eq_one_of_theta_eq hm
  · rw [← map_pow, ← map_pow, ← map_pow, hx, map_one, map_one, map_one]
  · rw [← map_pow, hζ, map_one]
  · rw [thetaAlgHom_apply, ACris.thetaField_iota, ACris.theta_algebraMap,
      WittVector.fontaineTheta_teichmuller, hu, thetaAlgHom_algClToBdR]
  · rw [thetaAlgHom_algClToBdR]; exact hζ0

theorem frob_ainfMap_teich (xb : OCb l) :
    Per6.ainfMap l (WittVector.teichmuller l xb) = WittVector.teichmuller l (Per6.tiltMap l xb) :=
  WittVector.map_teichmuller l _ _

theorem aB_teich (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : (c : Om l) ^ m = 1)
    (xb : OCb l)
    (hx : ∀ k : ℕ, ∃ y : OC l, (y : ℂ_[l]) ^ (l ^ k) = ((c : Om l) : ℂ_[l]) ∧ y ^ m = 1 ∧
      PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    Per6.aB l (WittVector.teichmuller l xb) = uB l c := by
  choose y h1 h2 h3 using hx
  have hco : m.Coprime l := ((Fact.out : l.Prime).coprime_iff_not_dvd.2 hl).symm
  obtain ⟨hp, hu⟩ := frob_tilt_root hm hco (Per6.tiltMap l xb) (fun k => Per6.intEquiv l (y k)) h1
    (fun k => by rw [← map_pow, h2, map_one]) (fun k => frob_coeff_tiltMap xb k (y k) (h3 k))
  apply ιCD_injective
  refine ((congrArg (ιCD l) (frob_aB_apply _)).trans (ιCD_cB _)).trans (Eq.trans ?_ (ιCD_uB c).symm)
  rw [cD_apply, frob_oD_apply, frob_ainfMap_teich, frob_iota_teich hm hc _ hp hu]

theorem frob_ainfMap_frobenius (a : Ainf l) :
    Per6.ainfMap l (WittVector.frobenius a) = WittVector.frobenius (Per6.ainfMap l a) := by
  ext n
  simp [Per6.ainfMap, WittVector.map_coeff, WittVector.coeff_frobenius_charP]

theorem frob_phi_ainfMap (a : Ainf l) :
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l (WittVector.frobenius a)) =
      ACris.phi ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) := by
  rw [ACris.phi_algebraMap, frob_ainfMap_frobenius]
  rfl

theorem aB_frobenius (a : Ainf l) : Per6.aB l (WittVector.frobenius a) = Per6.φB l (Per6.aB l a) :=
  ((frob_aB_apply _).trans (congrArg (Per6.cB l) (frob_phi_ainfMap a))).trans
    ((φB_cB _).symm.trans (congrArg (Per6.φB l) (frob_aB_apply a).symm))

end PositivityTheory.LocInh
end
end

-- bundled from Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
section
noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GaloisCommutant

section Abstract

variable {A B E : Type} [CommRing A] [CommRing B] [CommRing E] {a t : A} {f : A →+* B}

theorem comm_equiv (hf : IsFrac f a t) (ι : B →+* E) (s : B →+* B) (d : E ≃+* E)
    (e : ∀ x, ι (s (f x)) = d (ι (f x))) (b : B) : ι (s b) = d (ι b) :=
  RingHom.congr_fun (hf.hom_ext (g := ι.comp s) (h := (d : E →+* E).comp ι) e) b

theorem comm_self (hf : IsFrac f a t) (u s : B →+* B)
    (e : ∀ x, u (s (f x)) = s (u (f x))) (b : B) : u (s b) = s (u b) :=
  RingHom.congr_fun (hf.hom_ext (g := u.comp s) (h := s.comp u) e) b

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem toBot_one : Per6.toBot (1 : GQ l) = 1 := AlgEquiv.ext fun _ => rfl

theorem toBot_mul (g h : GQ l) : Per6.toBot (g * h) = Per6.toBot g * Per6.toBot h :=
  AlgEquiv.ext fun _ => rfl

theorem σD_eq (g : GQ l) : Per6.σD g = galBdRField (Per6.toBot g) := rfl

theorem σD_eq_smul (g : GQ l) (x : Per6.BdR l) : Per6.σD g x = Per6.toBot g • x := by
  rw [σD_eq, gal_smul_bDeRham_def]

theorem σD_algebraMap (g : GQ l) (y : Per6.BdRp l) :
    Per6.σD g (algebraMap (Per6.BdRp l) (Per6.BdR l) y) =
      algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.toBot g • y) := by
  rw [σD_eq, galBdRField_algebraMap]

theorem cD_galCris (g : GQ l) (x : ACris.ACris ℂ_[l] l) :
    cD l (ACris.galCris (Per6.toBot g) x) = Per6.σD g (cD l x) := by
  rw [cD_apply, cD_apply, σD_algebraMap, ← ACris.gal_smul_def, ACris.iota_gal_smul]

theorem ιCD_σB_aux (g : GQ l) (b : Per6.Bcris l) : ιCD l (Per6.σB g b) = Per6.σD g (ιCD l b) :=
  comm_equiv (cB_isFrac l) _ _ _ (fun x =>
    ((congrArg (ιCD l) (σB_cB g x)).trans (ιCD_cB _)).trans
      ((cD_galCris g x).trans (congrArg (Per6.σD g) (ιCD_cB x).symm))) b

theorem σD_one_aux (b : Per6.BdR l) : Per6.σD (1 : GQ l) b = b := by
  rw [σD_eq_smul, toBot_one, one_smul]

theorem σD_mul_aux (g h : GQ l) (b : Per6.BdR l) :
    Per6.σD (g * h) b = Per6.σD g (Per6.σD h b) := by
  rw [σD_eq_smul, σD_eq_smul, σD_eq_smul, toBot_mul, mul_smul]

theorem oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem phi_galCris (g : GQ l) (x : ACris.ACris ℂ_[l] l) :
    ACris.phi ℂ_[l] l (ACris.galCris (Per6.toBot g) x) =
      ACris.galCris (Per6.toBot g) (ACris.phi ℂ_[l] l x) := by
  rw [← ACris.gal_smul_def, ← ACris.gal_smul_def, ACris.phi_gal_smul]

theorem coe_χQ (g : GQ l) :
    ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) = ((cycloChar ⊥ (Per6.toBot g) : ℤ_[l]) : ℚ_[l]) := rfl

theorem cD_χA (g : GQ l) : cD l (Per6.χA (Per6.toBot g)) =
    oD l (algebraMap ℚ_[l] (Om l) ((χQ l g : ℚ_[l]ˣ) : ℚ_[l])) := by
  rw [cD_apply, Per6.χA, ACris.iota_padicInt, oD_apply, AlgHom.commutes, coe_χQ]

theorem cB_χA (g : GQ l) : Per6.cB l (Per6.χA (Per6.toBot g)) = qB l ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) :=
  ιCD_injective (((ιCD_cB _).trans (cD_χA g)).trans (ιCD_qB _).symm)

theorem tB_eq : tB l = Per6.cB l (Per6.tA l) := rfl

end GaloisCommutant

open GaloisCommutant

variable {l : ℕ} [Fact l.Prime]

theorem σB_one (b : Per6.Bcris l) : Per6.σB (1 : GQ l) b = b :=
  ιCD_injective ((ιCD_σB_aux 1 b).trans (σD_one_aux _))

theorem σB_mul (g h : GQ l) (b : Per6.Bcris l) : Per6.σB (g * h) b = Per6.σB g (Per6.σB h b) :=
  ιCD_injective (((ιCD_σB_aux (g * h) b).trans (σD_mul_aux g h _)).trans
    ((ιCD_σB_aux g _).trans (congrArg (Per6.σD g) (ιCD_σB_aux h b))).symm)

theorem σD_one (b : Per6.BdR l) : Per6.σD (1 : GQ l) b = b :=
  σD_one_aux b

theorem σD_mul (g h : GQ l) (b : Per6.BdR l) : Per6.σD (g * h) b = Per6.σD g (Per6.σD h b) :=
  σD_mul_aux g h b

theorem ιCD_σB (g : GQ l) (b : Per6.Bcris l) : ιCD l (Per6.σB g b) = Per6.σD g (ιCD l b) :=
  ιCD_σB_aux g b

theorem σD_oD (g : GQ l) (x : Om l) : Per6.σD g (oD l x) = oD l (g x) := by
  rw [oD_apply, oD_apply, σD_algebraMap, gal_smul_algClToBdR]
  rfl

theorem φB_σB (g : GQ l) (b : Per6.Bcris l) : Per6.φB l (Per6.σB g b) = Per6.σB g (Per6.φB l b) :=
  comm_self (cB_isFrac l) _ _ (fun x =>
    (((congrArg (Per6.φB l) (σB_cB g x)).trans (φB_cB _)).trans
      (congrArg (Per6.cB l) (phi_galCris g x))).trans
      ((congrArg (Per6.σB g) (φB_cB x)).trans (σB_cB g _)).symm) b

theorem σD_mem_FilD (g : GQ l) (a : ℤ) (x : Per6.BdR l) (hx : x ∈ Per6.FilD l a) :
    Per6.σD g x ∈ Per6.FilD l a := by
  rw [σD_eq_smul]
  exact (gal_smul_mem_fil_iff (Per6.toBot g) a x).2 hx

theorem σB_tB (g : GQ l) : Per6.σB g (tB l) = qB l ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) * tB l := by
  rw [tB_eq, σB_cB, Per6.galCris_tA, map_mul, cB_χA]

theorem χQ_cyc (g : GQ l) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    ∃ a : ℕ, ‖(χQ l g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a := by
  refine ⟨((cycloChar ⊥ (Per6.toBot g) : ℤ_[l]).toZModPow m).val, ?_,
    cycloChar_spec ⊥ (Per6.toBot g) hζ⟩
  rw [coe_χQ]
  generalize (cycloChar ⊥ (Per6.toBot g) : ℤ_[l]) = z
  have h1 : z - ((z.toZModPow m).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
    have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h1
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h2
  exact h2

end PositivityTheory.LocInh
end
end

