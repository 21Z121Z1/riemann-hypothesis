import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0059
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FramedForms

section Torsor

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem deco_smul (a : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) :
    (a • p).deco = (a.1, a.2.1) • p.deco := rfl

theorem fr_smul (a : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) (P : Q) :
    (a • p).fr P = a.1.1 * p.fr P * ((a.2.2 P)⁻¹).1 := rfl

theorem exists_smul_of_deco_eq {p q : DecoF E n ST SG Q} (h : p.deco = q.deco) :
    ∃ c : GLQ E n Q, q = ((1, 1, c) : UF E n × GLG E n SG × GLQ E n Q) • p := by
  have h' : p.1.1 = q.1.1 := h
  refine ⟨fun P => ⟨(q.fr P)⁻¹ * p.fr P, fun x => ?_⟩, ?_⟩
  · have h1 := q.2 P (((q.fr P)⁻¹ * p.fr P) x)
    have h2 : q.1.2 P (((q.fr P)⁻¹ * p.fr P) x) = p.1.2 P x :=
      LinearEquiv.apply_symm_apply (q.1.2 P) (p.1.2 P x)
    rw [h2, ← h'] at h1
    exact h1.symm.trans (p.2 P x)
  · apply Subtype.ext
    apply Prod.ext
    · exact h'.symm.trans (one_smul (UF E n × GLG E n SG) p.1.1).symm
    · funext P
      show q.fr P = (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((q.fr P)⁻¹ * p.fr P)⁻¹
      group

theorem stab_inj (p : DecoF E n ST SG Q) {a b : UF E n × GLG E n SG × GLQ E n Q}
    (ha : a • p = p) (hb : b • p = p) (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) : a = b := by
  refine Prod.ext h1 (Prod.ext h2 ?_)
  funext P
  have e1 : (a • p).fr P = (b • p).fr P := by rw [ha, hb]
  rw [fr_smul, fr_smul, h1] at e1
  exact inv_injective (Subtype.ext (mul_left_cancel e1))

end Torsor

section Form

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem incl_injective (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    Function.Injective (FrmG.incl Λ Θ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Subtype.ext h3))

theorem grp_finiteIndex (Θ : LevQFam X.E X.K n Q) (h : ∀ R : Q, (Θ R).H.FiniteIndex) :
    Θ.grp.FiniteIndex := by
  have h1 : ∀ R : Q, ((Θ R).H.comap (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)).FiniteIndex := by
    intro R
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective _ (Function.surjective_eval R)]
    exact (h R).index_ne_zero
  have h2 := Subgroup.finiteIndex_iInf h1
  refine Subgroup.finiteIndex_of_le (H := ⨅ R : Q, (Θ R).H.comap
    (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)) ?_
  intro c hc
  exact (Subgroup.mem_pi _).mpr fun R _ => Subgroup.mem_iInf.mp hc R

theorem chr_root (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) ^ m = 1 := by
  obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2.1
  obtain ⟨k, hk, hk'⟩ := hΘ g.2.2
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  have hk2 : ((Θ.chr g.2.2 : X.Kˣ) : X.K) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk', Units.val_one]
  rw [Units.val_mul, mul_pow, pow_mul, hc, one_pow, one_mul, mul_comm m k, pow_mul, hk2, one_pow]

theorem frmGSD_ok (hX : X.Ok) (C : CoefPk X n (DecoSet X.E n ST SG)) (hC : C.Eqv)
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (hfi : ∀ R : Q, (Θ R).H.FiniteIndex)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).Ok where
  fin_orb := by
    obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have := grp_finiteIndex Θ hfi
    let T : Set (DecoSet X.E n ST SG) := {d | d ∈ s ∧ ∃ p : DecoF X.E n ST SG Q, p.deco = d}
    have hT : Finite T := hs.subset fun d hd => hd.1
    let S := frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ
    refine Finite.of_surjective (fun x : T × (GLQ X.E n Q ⧸ Θ.grp) =>
      S.cls (((1, 1, (x.2.out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • x.1.2.2.choose)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)
      have hq : (((g⁻¹, 1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q)).deco = d0 := by
        rw [deco_smul, hg, smul_smul]
        simp only [Prod.mk_mul_mk, inv_mul_cancel, mul_one]
        exact one_smul (UF X.E n × GLG X.E n SG) d0
      have hd : d0 ∈ T := ⟨hd0, _, hq⟩
      obtain ⟨c, hc⟩ := exists_smul_of_deco_eq (hd.2.choose_spec.trans hq.symm)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Θ.grp c⁻¹
      refine ⟨(⟨d0, hd⟩, (c⁻¹ : GLQ X.E n Q)), ?_⟩
      refine (S.cls_eq_iff _ p).mpr ⟨((g⁻¹, 1, h⁻¹) : FrmG Λ Θ), ?_⟩
      show ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q) =
        ((1, 1, ((c⁻¹ : GLQ X.E n Q) : GLQ X.E n Q ⧸ Θ.grp).out⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) •
          hd.2.choose
      have e1 : ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) =
          (1, 1, (h : GLQ X.E n Q)⁻¹) * (g⁻¹, 1, 1) := by simp
      rw [e1, mul_smul, hc, smul_smul, hh]
      simp
  fin_stab := by
    intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).G p =>
        (⟨((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG X.E n SG) (DecoF.deco p))) ?_
    intro a b hab
    have h0 := congrArg Subtype.val hab
    exact Subtype.ext (incl_injective Λ Θ
      (stab_inj p a.2 b.2 (Prod.mk.inj h0).1 (Prod.mk.inj h0).2))
  nab_smul := by
    intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.nab_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  del_smul := by
    intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.del_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  inv := by
    intro g x y
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    show C.pair (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 x)
      (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv g.1 x y, smul_smul]
    show (star ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem main : ∀ {X : Fields} (_ : X.Ok) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (lam : X.Tau → DomWeight n) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q),
    (∀ R : Q, (Θ R).H.FiniteIndex) → (∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) →
    (frmGSD ((roundPk X lam fun d : DecoSet X.E n ST SG => d.1.Lsh).pull DecoF.deco) Λ Θ).Ok := by
  intro X hX n ST SG Q lam Λ Θ h1 h2
  exact frmGSD_ok hX _
    ⟨fun a d => roundPk_nab X _ _ (d.1.Lsh_act a.1.2 a.2), fun a d => roundPk_del X _ _ (d.1.Lsh_act a.1.2 a.2),
      roundPk_inv X _ _ hX.emb_star⟩ Λ Θ h1 h2

end Form

end GlobalTheory.FramedForms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

theorem exists_mem_one_sub_loc_dvd {R : Type} [CommRing R] [IsDedekindDomain R] (S : Finset (HeightOneSpectrum R))
    (I : Ideal R) (hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal) (c : R) [Finite (R ⧸ Ideal.span {c})] :
    ∃ s ∈ I, ∃ t r : R, (∀ P ∈ S, t ∉ P.asIdeal) ∧ t * (1 - s) = c * r := by
  have h1 : I ⊔ (⨅ P ∈ S, P.asIdeal) = ⊤ := by
    refine Ideal.sup_iInf_eq_top fun P hP => ?_
    obtain ⟨s, hs, hsP⟩ := hI P hP
    by_contra hne
    have := P.isMaximal.eq_of_le hne le_sup_right
    exact hsP (this ▸ (le_sup_left : I ≤ I ⊔ P.asIdeal) hs)
  have h2 : (1 : R) ∈ I ⊔ (⨅ P ∈ S, P.asIdeal) := h1 ▸ Submodule.mem_top
  obtain ⟨s0, hs0, π, hπ, hsum⟩ := Submodule.mem_sup.1 h2
  have hπ' : ∀ P ∈ S, π ∈ P.asIdeal := by
    intro P hP
    exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hπ P) hP
  have key : ∃ i j : ℕ, i < j ∧ Ideal.Quotient.mk (Ideal.span {c}) (π ^ i) = Ideal.Quotient.mk (Ideal.span {c}) (π ^ j) := by
    obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun i : ℕ => Ideal.Quotient.mk (Ideal.span {c}) (π ^ i))
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact ⟨i, j, h', h⟩
    · exact ⟨j, i, h', h.symm⟩
  obtain ⟨i, j, hij, h⟩ := key
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨1 - π ^ i, ?_, 1 - π ^ (d + 1), r, ?_, ?_⟩
  · have : (1 - π) ∣ 1 - π ^ i := by simpa using sub_dvd_pow_sub_pow (1 : R) π i
    obtain ⟨u, hu⟩ := this
    have hs : 1 - π = s0 := by rw [← hsum]; ring
    rw [hu, hs]
    exact I.mul_mem_right _ hs0
  · intro P hP hmem
    have : π ^ (d + 1) ∈ P.asIdeal := P.asIdeal.pow_mem_of_mem (hπ' P hP) _ (Nat.succ_pos d)
    have h1 : (1 : R) ∈ P.asIdeal := by simpa using P.asIdeal.add_mem hmem this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rw [← hr]; ring

theorem finite_divLat_quot_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA cB : ℕ), Submodule.IsLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < cB → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) := by
  intro E _ _ _ a b S N N' cA cB hN hN' hA hB
  classical
  obtain ⟨G, hG⟩ := hN.fg
  have hA' : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (cB : E) ≠ 0 := by exact_mod_cast hB.ne'
  have memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  have memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔
      ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x := fun x => Iff.rfl
  have memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  let ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b) :=
    { toFun := fun x g => (cA : 𝓞 E) • x g
      map_add' := by intro x y; funext g; simp
      map_smul' := by intro r x; funext g; simp [smul_comm r] }
  have ev_inj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hsp : Submodule.span E (G : Set (Sp E a)) = ⊤ := by
      rw [← hN.span_eq_top, ← hG, Submodule.span_span_of_tower]
    refine LinearMap.ext_on hsp fun g hg => ?_
    have := congrFun hx ⟨g, hg⟩
    have h2 : (cA : E) • x g = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact this
    simpa [hA'] using (smul_eq_zero.1 h2).resolve_left hA'
  let T : Submodule (𝓞 E) (G → Sp E b) := Submodule.pi Set.univ fun _ => N'
  have hT : T.FG := Submodule.fg_pi fun _ => hN'.fg
  let Z : Submodule (𝓞 E) (HomE E a b) := T.comap ev
  have memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N' := fun x =>
    ⟨fun h g => h g trivial, fun h g _ => h g⟩
  have hZ : Z.FG := by
    have : Module.Finite (𝓞 E) T := Module.Finite.iff_fg.2 hT
    have : Module.Finite (𝓞 E) Z := Module.Finite.of_injective (ev.restrict (p := Z) (q := T) fun x hx => hx) (by
      intro x y hxy
      exact Subtype.ext (ev_inj (congrArg Subtype.val hxy)))
    exact Module.Finite.iff_fg.1 this
  have hZD : Z ≤ divLat cA (homAt S N N') := by
    intro x hx
    rw [memD]
    intro P hP y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
    have : ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N' := by
      intro w hw
      rw [← hG] at hw
      induction hw using Submodule.span_induction with
      | mem g hg => exact (memZ x).1 hx ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, smul_add]; exact N'.add_mem hu hv
      | smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]; exact N'.smul_mem r hu
    refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
    have h := this _ hsy
    rwa [LinearMap.map_smul_of_tower, smul_comm] at h
  have : Module.Finite (𝓞 E) Z := Module.Finite.iff_fg.2 hZ
  have hc : ((cB : 𝓞 E) * cA) ≠ 0 := by
    have : cB * cA ≠ 0 := by positivity
    exact_mod_cast this
  have : Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)
  have hsurj : Function.Surjective
      (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let I : Ideal (𝓞 E) := Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
    have hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal := by
      intro P hP
      have h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N' := fun g =>
        (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))
      choose f hf hf' using h1
      refine ⟨∏ g, f g, ?_, ?_⟩
      · show (∏ g, f g) • x ∈ Z
        rw [memZ]
        intro g
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]
        exact N'.smul_mem _ (hf' g)
      · intro h
        have := P.isPrime
        obtain ⟨g, _, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
        exact hf g hg
    obtain ⟨s, hs, t, r, ht, htr⟩ := exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)
    refine ⟨⟨s • x, hs⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show x - s • x ∈ mulLat cB (homAt S N N')
    have hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W),
        (cB : 𝓞 E) • (cB : E)⁻¹ • w = w := by
      intro W _ _ _ w
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩
    rw [memH]
    intro P hP y hy
    obtain ⟨u, hu, huy⟩ := (mem_locP P N' _).1 ((memD x).1 hx P hP y hy)
    refine (mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩
    have e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y := by
      have e2 : (x - s • x) y = (1 - s) • x y := by simp [sub_smul]
      rw [LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]
    rw [mul_smul, e1, smul_comm]
    exact N'.smul_mem r huy
  have := Module.Finite.of_surjective _ hsurj
  have : Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
    Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
  rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')
  rw [memM]
  exact ⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusDecompositionUnramifiedPrimeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_decomposition_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) → ∃ (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 ∧ (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) = p ^ orderOf φ ∧ (∀ g : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, g • x ∈ Q.asIdeal ↔ x ∈ Q.asIdeal) ↔ g ∈ Subgroup.zpowers φ) ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ Q'.asIdeal → ∃ g : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, x ∈ Q'.asIdeal ↔ g • x ∈ Q.asIdeal := by
  first | exact @GlobalTheory.UnramifiedFrobenius.exists_frobenius | exact GlobalTheory.UnramifiedFrobenius.exists_frobenius | (intros; apply GlobalTheory.UnramifiedFrobenius.exists_frobenius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusNontrivialOnInertQuadraticStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_nontrivial_on_inert_quadratic : ∀ (E : Type) [Field E] [NumberField E] (M : Subfield E) (p : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → Module.finrank ℚ M = 2 → (Ideal.span {((p : ℕ) : 𝓞 M)}).IsPrime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → ∃ x ∈ M, φ x ≠ x := by
  first | exact @GlobalTheory.frobenius_moves_quadratic_subfield_of_inert | exact GlobalTheory.frobenius_moves_quadratic_subfield_of_inert | (intros; apply GlobalTheory.frobenius_moves_quadratic_subfield_of_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisIndexTwoCmConjugationStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_index_two_cm_conjugation : ∀ (X : Formalism.L2.Col.Fields), X.Core → IsGalois ℚ X.E → ∃ (τ₀ : X.Tau) (H : Subgroup (X.E ≃ₐ[ℚ] X.E)) (γ : H ≃ X.Tau) (c : X.E ≃ₐ[ℚ] X.E), H.index = 2 ∧ (∀ g ∈ H, ∀ x ∈ X.Kq, g x = x) ∧ (∀ (h : H) (x : X.E), X.emb (γ h) x = X.emb τ₀ (h.1 x)) ∧ (∀ x, c x = star x) ∧ c ∉ H := by
  first | exact @GlobalTheory.cmType_equiv_fixingSubgroup | exact GlobalTheory.cmType_equiv_fixingSubgroup | (intros; apply GlobalTheory.cmType_equiv_fixingSubgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenMDetNeZeroOfNontrivial
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem jacobi_blocks_of_mul {R : Type} [CommRing R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (M Y : Matrix (α ⊕ β) (α ⊕ β) R) (d : R) (h : M * Y = d • (1 : Matrix (α ⊕ β) (α ⊕ β) R)) :
    M.toBlocks₁₁.det * Y.det = d ^ Fintype.card α * Y.toBlocks₂₂.det := by
  have hY : Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Y).symm
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks M).symm
  have h' := h
  rw [hM, hY, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero] at h'
  obtain ⟨h11, h12, -, -⟩ := Matrix.fromBlocks_inj.mp h'
  have key : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 1 * Y =
      Matrix.fromBlocks (d • 1) 0 Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    conv_lhs => rw [hY]
    rw [Matrix.fromBlocks_multiply, h11, h12]
    simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
    Matrix.det_smul, Matrix.det_one, mul_one] at hd
  exact hd

theorem genM_det_ne_zero_of_nontrivial (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  have hm : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [RingHom.map_det, hm, Matrix.det_one, map_zero] at h1
  exact one_ne_zero h1

theorem exists_equiv_castLE_rev {n s : ℕ} (hs : s ≤ n) : ∃ e : Fin (n - s) ⊕ Fin s ≃ Fin n,
    (∀ a, e (.inl a) = Fin.castLE (Nat.sub_le n s) a) ∧ ∀ q, e (.inr q) = Fin.rev (Fin.castLE hs q) := by
  refine ⟨(Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans
    (finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hs))), ?_, ?_⟩
  · intro a
    ext
    simp
  · intro q
    have hq := q.isLt
    ext
    simp
    omega

theorem jacobi_adjugate_perm {R : Type} [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (h1 : 1 ≤ s)
    (M : Matrix (Fin n) (Fin n) R) (hM : M.det ≠ 0) (σ : Equiv.Perm (Fin n)) : ∃ ε : ℤˣ,
    (Matrix.of fun q p : Fin s => M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det =
      (ε : ℤ) • (M.det ^ (s - 1) * (Matrix.of fun a b : Fin (n - s) =>
        M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det) := by
  obtain ⟨e, he1, he2⟩ := exists_equiv_castLE_rev hs
  obtain ⟨f, hf1, hf2⟩ : ∃ f : Fin (n - s) ⊕ Fin s ≃ Fin n,
      (∀ a, f (.inl a) = σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) ∧ ∀ p, f (.inr p) = σ (Fin.castLE hs p) :=
    ⟨(e.trans Fin.revPerm).trans σ, fun a => by simp [he1], fun p => by simp [he2]⟩
  have hmul : M.submatrix f e * M.adjugate.submatrix e f =
      M.det • (1 : Matrix (Fin (n - s) ⊕ Fin s) (Fin (n - s) ⊕ Fin s) R) := by
    rw [← Matrix.submatrix_mul M M.adjugate f e f e.bijective, Matrix.mul_adjugate]
    ext i j
    simp [Matrix.one_apply]
  have hJ := jacobi_blocks_of_mul _ _ _ hmul
  have hC : (M.submatrix f e).toBlocks₁₁ = Matrix.of fun a b : Fin (n - s) =>
      M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hf1, he1]
  have hT : (M.adjugate.submatrix e f).toBlocks₂₂ = Matrix.of fun q p : Fin s =>
      M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p)) := by
    ext q p
    simp [Matrix.toBlocks₂₂, hf2, he2]
  have hY : (M.adjugate.submatrix e f).det =
      ((Equiv.Perm.sign (e.trans f.symm) : ℤ) : R) * M.det ^ (n - 1) := by
    have hre : M.adjugate.submatrix e f = (M.adjugate.submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j
      simp
    rw [hre, Matrix.det_permute, Matrix.det_submatrix_equiv_self, Matrix.det_adjugate, Fintype.card_fin]
  rw [hC, hT, hY, Fintype.card_fin] at hJ
  have hpow : M.det ^ (n - 1) = M.det ^ (n - s) * M.det ^ (s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hJ
  refine ⟨Equiv.Perm.sign (e.trans f.symm), ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (n - s) hM)
  rw [zsmul_eq_mul]
  linear_combination -hJ

theorem cofAct_initMinor : ∀ (R : Type) [CommRing R] [IsDomain R] (n s : ℕ) (hs : s ≤ n), 1 ≤ s → ∀ σ : Equiv.Perm (Fin n), ∃ ε : ℤˣ, cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) = (ε : ℤ) • ((genM R n).det ^ (s - 1) * initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s)) := by
  intro R _ _ n s hs h1 σ
  obtain ⟨ε, hε⟩ := jacobi_adjugate_perm hs h1 (genM R n) (genM_det_ne_zero_of_nontrivial R n) σ
  refine ⟨ε, ?_⟩
  have hlhs : cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) =
      (Matrix.of fun q p : Fin s => (genM R n).adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
    rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext q p
    simp [cofAct]
  have hrhs : (Matrix.of fun a b : Fin (n - s) =>
      genM R n (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det =
      initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s) := by
    rw [initMinor]
    congr 1
  rw [hlhs, hε, hrhs]

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem goodO_finExt_integers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  GlobalTheory.Pass.goodO_ringOfIntegers

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpWindowOfJumpSetsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  first | exact @GlobalTheory.BlockWindow.jumpWindow_of_jumpSets | exact GlobalTheory.BlockWindow.jumpWindow_of_jumpSets | (intros; apply GlobalTheory.BlockWindow.jumpWindow_of_jumpSets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedMuPartInBaseChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_mu_part_in_base_change : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.adm5 D → SumRepresentations.adm7 D → GlobalTheory.RowCopy.RowSize D → GlobalTheory.RowCopy.HeckeSplitOne D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa → (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  first | exact @GlobalTheory.MuBlock.mu_block_mem | exact GlobalTheory.MuBlock.mu_block_mem | (intros; apply GlobalTheory.MuBlock.mu_block_mem <;> assumption)
end

