import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PerLaw

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem piT_notMem_Q (h : I.Ok) (u : B.Word) (a : I.ι) (P : I.Q a) : (B.primes X).piT u ∉ P.1.asIdeal := fun hm => by
  have hPr := (base_fields_primes_ok B X).2.1
  refine T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u) P.1 P.2 ?_
  rw [← hPr.piT_norm u]
  exact P.1.asIdeal.mul_mem_right _ hm

theorem til_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b : (I.perIn u a).S'.β) (p : (I.stX a).D b) :
    ((I.perIn u a).til b p).1.1.deco = DecoSet.tilH (N_m_succ B.R) ((B.primes X).piT u) p.1.1.deco :=
  tilF_deco I.sel (I.tup a) (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) p.1.1

theorem pref_m (u : B.Word) (a : I.ι) (b : (I.stp0 u a B.R.m).β) (q : (I.stp0 u a B.R.m).D b) :
    I.pref u a B.R.m b q ↔ ∃ d, q.1.1 = tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d := by
  have hm := B.R.two_le_m
  rw [← topLev_pref_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps u]
  exact ⟨fun h => h.2.2, fun h => ⟨fun e => by omega, fun e => by omega, h⟩⟩

theorem stX_ok (a : I.ι) : (I.stX a).Ok :=
  stepY_ok (Ys.triv B.fields _) Unit (fun _ => rowTyG I.Ch I.Ps) (fun _ => levQX B.R I.sel (I.tup a)) (fun _ => True)
    (base_fields_primes_ok B X).1 (fun _ => levQX_finiteIndex I.sel (I.tup a))
    (fun _ P g => (levQX_root (R := B.R) I.sel (I.tup a) P).imp fun _ hm => ⟨hm.1, hm.2 g⟩) fun _ _ => Set.finite_singleton _

set_option maxHeartbeats 1600000 in

theorem perIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Ok where
  step := stX_ok a
  til_smul _ g p := Subtype.ext (Prod.ext
    (tilF_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) g p.1.1)
    (Set.image_empty _).symm)
  ext_inj _ := extTop_injective I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  gam_ini _ g x := (congrArg (iniH (N_m_succ B.R)) (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x)).trans
    ((iniH_extUH _ g.1 x).trans (toGLm_mulVec g.1.1 _).symm)
  gam_last _ g x := (congrFun (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x) _).trans (extUH_last _ g.1 x)
  chr_ext _ g := chr_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps g
  tz_ne := by
    have hPr := (base_fields_primes_ok B X).2.1
    show star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) ≠ 0
    rw [star_ne_zero]
    intro h
    have h1 : (B.primes X).piT u = 0 := RingOfIntegers.ext h
    have h2 := hPr.piT_norm u
    rw [h1, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  Lsh_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.Lsh ↔ _
    rw [til_deco h u a b p]
    exact tilH_Lsh _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
      (fun P => decoFin_mem_of_mem_divs P.2) (piT_dvd_of_mem (base_fields_primes_ok B X).1 hPr u) x
  rep_til b p := by
    obtain ⟨d, hd⟩ := (pref_m u a _ _).1 (@pref_prefRep _ _ _ ((I.stp0 u a B.R.m).actD _)
      (I.pref u a B.R.m (idxTop I.sel (I.tup a) (I.idx a))) ((I.perIn u a).til b p) ((pref_m u a _ _).2 ⟨p.1.1, rfl⟩))
    exact ⟨(), trivPt _ _ _ _ _ d, (topPt_val I.sel (I.tup a) (I.cst a) u _).symm.trans
      (congrArg (topPt I.sel (I.tup a) (I.cst a) u) hd)⟩
  H_idx _ := (inferInstance : (⊤ : Subgroup _).FiniteIndex)
  H_rat _ g := ⟨g, Subgroup.mem_top _, rfl⟩

set_option maxHeartbeats 1600000 in

theorem perIn_over (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Over (I.atIn u a) where
  norm_tz := by
    show star (star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E)) *
      star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).T u : B.fields.E)
    rw [star_star]
    have h := congrArg (algebraMap (𝓞 B.fields.E) B.fields.E) ((base_fields_primes_ok B X).2.1.piT_norm u)
    rw [map_mul, map_natCast] at h
    exact h
  N_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.N ↔ _
    rw [til_deco h u a b p]
    exact tilH_N _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) x
  f_til b p P x hx := by
    have hPr := (base_fields_primes_ok B X).2.1
    change x ∈ ((I.perIn u a).til b p).1.1.deco.1.N at hx
    show ((I.perIn u a).til b p).1.1.deco.1.f P x = _
    rw [til_deco h u a b p] at hx ⊢
    exact tilH_f _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) P x hx

theorem perIn_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok →
    ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) :=
  fun _ h u a => ⟨perIn_ok h u a, perIn_over h u a⟩

end GlobalTheory.Mem.Col2.PerLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtLevel

def underT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal} :=
  ⟨P.1.under (𝓞 X.F), by
    show algebraMap (𝓞 X.F) (𝓞 X.E) _ ∈ P.1.asIdeal
    rw [map_natCast]
    exact T_mem_vT hPr u P⟩

theorem underT_bijective {Z : Dat} (hX : Z.X.Ok) (hPr : Z.Pr.Ok) (u : Z.Pr.Word) : Function.Bijective (underT hPr u) := by
  constructor
  · intro P Q h
    have h1 : P.1.asIdeal.under (𝓞 Z.X.F) = Q.1.asIdeal.under (𝓞 Z.X.F) :=
      congrArg (fun v => v.1.asIdeal) h
    rcases GlobalTheory.CharVal.eq_or_eq_conjP hX (GlobalTheory.CharVal.splitOver_vT hX hPr u Q.2).ne h1 with e | e
    · exact Subtype.ext e
    · refine absurd ?_ (conj_piT_notMem hPr u Q)
      have := decoFin_mem_of_mem_divs P.2
      rw [e, mem_conjP] at this
      exact this
  · rintro ⟨v, hv⟩
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 Z.X.E) v.asIdeal
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ Q := by
      rw [hQv.over, Ideal.under_def, Ideal.mem_comap, map_natCast] at hv
      exact hv
    have hne : Q ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hT
      exact (hPr.T_prime u).ne_zero (by exact_mod_cast hT)
    let P : HeightOneSpectrum (𝓞 Z.X.E) := ⟨Q, hQ.isPrime, hne⟩
    rw [← hPr.piT_norm u] at hT
    rcases hQ.isPrime.mem_or_mem hT with h | h
    · exact ⟨⟨P, (mem_divs (hPr.piT_ne_zero u) P).2 h⟩, Subtype.ext (HeightOneSpectrum.ext hQv.over.symm)⟩
    · exact ⟨⟨conjPrime₂ P, (mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP P _).2 h)⟩,
        Subtype.ext (HeightOneSpectrum.ext ((GlobalTheory.CharVal.under_conjP hX P).trans hQv.over.symm))⟩

theorem seenBar_of_not {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (hs : ¬ seenC Pr u w) (τ : X.Tau) :
    X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
  rw [← map_natCast (X.embO τ), ← hPr.piT_norm u, map_mul] at hw
  refine (w.isPrime.mem_or_mem hw).resolve_left fun h => hs fun τ' => ?_
  rw [show X.embO τ' (Pr.piT u) = X.embO τ (Pr.piT u) from RingOfIntegers.ext (hPr.piT_Kq u _ _)]
  exact h

theorem mk_surj {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) : Function.Surjective (Ideal.Quotient.mk P.asIdeal) :=
  Ideal.Quotient.mk_surjective

theorem mk_zero {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) : x ∈ P.asIdeal ↔ Ideal.Quotient.mk P.asIdeal x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.symm

set_option maxHeartbeats 1000000 in

def atTTied {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    AtTTied (D := (I.rec7 l Z)) u where
  eV := Equiv.ofBijective (underT l.pr u)
    (underT_bijective (Z := B.dat X I.Ch) (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u)
  piU := X.piT u
  piU_K := X.piT_K u
  piU_norm := X.piT_norm u
  piU_cong := Ideal.mem_span_singleton.2 (X.piT_cong u)
  res := I.resT l u I.mu0
  res_surj v := mk_surj (X := B.fields) v.1
  res_pi v := (mk_zero (X := B.fields) v.1 _).1 (decoFin_mem_of_mem_divs (A := 𝓞 B.fields.E) v.2)
  res_conj v pb h e := by
    have h1 : pb = B.fields.conjO (X.piT u) := RingOfIntegers.ext (h.trans (B.fields_conjO_coe _).symm)
    exact conj_piT_notMem l.pr u v (h1 ▸ Ideal.Quotient.eq_zero_iff_mem.1 e)
  res_v v x := mk_zero (X := B.fields) v.1 _
  tauOf w hw v x := by
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    exact (tauAt_mem_iff l.pr u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 hw' v x).symm.trans
      (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).symm
  seenP w hw τ := by
    classical
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    have hs : (((I.rec7 l Z).fm u).seenP w = true) ↔ seenC (B.primes X) u w := decide_eq_true_iff
    by_cases h : seenC (B.primes X) u w
    · rw [if_pos (hs.2 h)]
      exact (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (h τ)
    · rw [if_neg (mt hs.1 h)]
      have h2 := (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (seenBar_of_not l.pr u hw' h τ)
      have h3 : ((B.fields.embO τ (B.fields.conjO (X.piT u)) : 𝓞 B.LL) : B.LL) = B.fields.emb τ (B.host.conj (X.piT u : B.host.E)) :=
        congrArg (B.fields.emb τ) (B.fields_conjO_coe _)
      exact h3 ▸ h2

theorem exists_atTTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ u : B.Word, ∃ A : AtTTied (D := (I.rec7 l Z)) u, I.IdV l u I.mu0 A.eV ∧ A.piU = X.piT u ∧ A.res = I.resT l u I.mu0 :=
  fun I _ _ l Z u => ⟨atTTied I l Z u, fun _ => rfl, rfl, by unfold atTTied; rfl⟩

end GlobalTheory.Mem.AtLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InertPlaceConj

open GlobalTheory.SelfDualGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isInertAt_of_not_split (w : HeightOneSpectrum (𝓞 E))
    (hu : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (hs : ¬ IsSplitAt w) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w := by
  classical
  haveI := w.isPrime
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = w.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal).1 hu).2
  have h2 : ¬ (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (w.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = w.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    let u : HeightOneSpectrum (𝓞 E) := ⟨p, hpp, hp0⟩
    have hu' : u.under (𝓞 (maximalRealSubfield E)) = v := by
      ext1
      exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
        (Ideal.map_le_iff_le_comap.1 hpl)).symm
    by_contra hne
    exact hs ⟨u, fun h => hne (congrArg HeightOneSpectrum.asIdeal h), hu'⟩
  obtain ⟨n, hn⟩ : ∃ n, I = w.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact w.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_sub_conj_notMem_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ x : 𝓞 E, x - IsCMField.ringOfIntegersComplexConj E x ∉ w.asIdeal := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have := v.isPrime
  have := w.isPrime
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[maximalRealSubfield E] E) v.asIdeal w.asIdeal
  have hsq : ¬ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ w.asIdeal ^ 2 := by
    rw [h']
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[maximalRealSubfield E] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff (le_of_eq h')).1 hsq)] at hcard
  by_contra hn
  push_neg at hn
  have hs : IsCMField.complexConj E ∈ w.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) :=
    AddSubgroup.mem_inertia.2 fun x => by
      have := w.asIdeal.neg_mem (hn x)
      rw [neg_sub] at this
      exact this
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact IsCMField.complexConj_ne_one E hs

theorem exists_isUnramInv_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      IsUnramInv ϖ s (Ideal.absNorm (w.under (𝓞 (maximalRealSubfield E))).asIdeal) := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w w := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨GlobalTheory.InertConj.conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := GlobalTheory.InertConj.conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv w _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ w.asIdeal ^ 2 := by
    by_contra hn
    push_neg at hn
    have h1 : w.asIdeal ≤ w.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ w.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous w (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2']
  have hres : ∃ x, Valued.v x ≤ 1 ∧ Valued.v ((σ : w.adicCompletion E →+* w.adicCompletion E) x - x) = 1 := by
    obtain ⟨x, hx⟩ := exists_sub_conj_notMem_of_inert w h
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact w.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hx)
  have hfix : (σ : w.adicCompletion E →+* w.adicCompletion E)
      (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) =
      algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) := by
    change σ _ = _
    rw [σ2']
    congr 1
    exact IsCMField.complexConj_apply_eq_self E (s : maximalRealSubfield E)
  have hunif : IsUnifV E w (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) := by
    unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq w hs1 hs2
  refine ⟨σ, _, σ2', hinv, σ3, hfix, hunif, ?_, ?_, ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := hres
    exact ⟨x, hx1, hx2⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← h', Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue w

theorem exists_conj_isUnramInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  intro E _ _ _ w hu hs
  obtain ⟨s, ϖ, h1, h2⟩ := exists_isUnramInv_of_inert w (isInertAt_of_not_split w hu hs)
  exact ⟨s, ϖ, _, h1, h2⟩

end GlobalTheory.InertPlaceConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightFiltrationStrandDecomposition
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp.SubStab

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem rho_pow_N_apply (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) :
    a.ρ σ ((a.N ^ j) v) = (((normV w : ℕ) : ℂ) ^ deg σ) ^ j • (a.N ^ j) (a.ρ σ v) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, a.comm_apply, ih, map_smul, smul_smul,
      Module.End.mul_apply, pow_succ']

theorem rho_mem_ker_pow (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) (hv : (a.N ^ j) v = 0) :
    (a.N ^ j) (a.ρ σ v) = 0 := by
  have h1 := rho_pow_N_apply a σ⁻¹ j (a.ρ σ v)
  have h2 : a.ρ σ⁻¹ (a.ρ σ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h2, hv, smul_zero] at h1
  have h3 : a.ρ σ (a.ρ σ⁻¹ ((a.N ^ j) (a.ρ σ v))) = (a.N ^ j) (a.ρ σ v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← h3, h1, map_zero]

theorem pow_N_mem_wtSpace (a : WDRep h V)
    (hN : ∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) (j : ℕ) (k : ℤ) (v : V)
    (hv : v ∈ wtSpace a k) : (a.N ^ j) v ∈ wtSpace a (k + 2 * (j : ℤ)) := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    have e : k + 2 * ((j + 1 : ℕ) : ℤ) = (k + 2 * (j : ℤ)) + 2 := by push_cast; ring
    rw [e, pow_succ', Module.End.mul_apply]
    exact hN _ _ ih

theorem strand_and_lowPart_stable : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) → (∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m) ∧ IsSubWD a (lowPart (wtSpace a) a.N m) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a m hρ hN htop
  refine ⟨⟨fun σ => ?_, ?_⟩, ⟨fun σ => ?_, ?_⟩⟩
  ·
    show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap (a.ρ σ)
    refine iSup_le fun j => ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Submodule.mem_comap]
    rw [rho_pow_N_apply]
    refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨a.ρ σ s, hρ _ σ s hs, rfl⟩)
  ·
    show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap a.N
    refine iSup_le fun j => ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Submodule.mem_comap]
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hj : (j : ℕ) < m
    · exact Submodule.mem_iSup_of_mem (⟨(j : ℕ) + 1, by omega⟩ : Fin (m + 1)) ⟨s, hs, rfl⟩
    · have hjm : (j : ℕ) = m := by have := j.isLt; omega
      have hmem := pow_N_mem_wtSpace a hN ((j : ℕ) + 1) _ s hs
      rw [htop _ (by push_cast; omega), Submodule.mem_bot] at hmem
      rw [hmem]
      exact Submodule.zero_mem _
  ·
    show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap (a.ρ σ)
    refine iSup_le fun k => ?_
    rintro v ⟨hv1, hv2⟩
    exact Submodule.mem_iSup_of_mem k ⟨hρ k σ v hv1, rho_mem_ker_pow a σ _ v hv2⟩
  ·
    show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap a.N
    refine iSup_le fun k => ?_
    rintro v ⟨hv1, hv2⟩
    refine Submodule.mem_iSup_of_mem (k + 2) ⟨hN k v hv1, ?_⟩
    show (a.N ^ (((m : ℤ) - (k + 2) + 1) / 2).toNat) (a.N v) = 0
    have hv2' : (a.N ^ (((m : ℤ) - k + 1) / 2).toNat) v = 0 := hv2
    have hle : (((m : ℤ) - k + 1) / 2).toNat ≤ (((m : ℤ) - (k + 2) + 1) / 2).toNat + 1 := by omega
    rw [← Module.End.mul_apply, ← pow_succ, ← Nat.sub_add_cancel hle, pow_add,
      Module.End.mul_apply, hv2', map_zero]

end GlobalTheory.WeilDeligne.PrimDecomp.SubStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneDirectSumOfCompl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem wd_mk_eq_lpSum_restrict_of_isCompl {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (S T : Submodule ℂ V) (hS : IsSubWD a S) (hT : IsSubWD a T)
    (hST : IsCompl S T) :
    WD.mk a = (WD.mk (restrict a S hS)).lpSum (WD.mk (restrict a T hT)) := by
  rw [WD.lpSum_mk]
  symm
  apply WD.sound
  refine ⟨Submodule.prodEquivOfIsCompl S T hST, ?_, ?_⟩
  · rintro σ ⟨x, y⟩
    simp only [WDRep.sum_ρ, LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl',
      map_add, restrict_ρ_apply]
  · rintro ⟨x, y⟩
    simp only [WDRep.sum_N, LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl',
      map_add, restrict_N_apply]

theorem sumiso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (S T : Submodule ℂ V) (hS : IsSubWD a S) (hT : IsSubWD a T), IsCompl S T → WD.mk a = (WD.mk (restrict a S hS)).lpSum (WD.mk (restrict a T hT)) :=
  fun _ _ _ _ _ _ _ A w h V _ _ _ a S T hS hT hST =>
    wd_mk_eq_lpSum_restrict_of_isCompl A w h V a S T hS hT hST

end GlobalTheory.WeilDeligne.PrimDecomp
end

