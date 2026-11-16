/-!
# Formal spec of the memory-leak test verdict logic

This file is the normative specification for the verdict rules that
`tests/memory/memory_leak_tests.py` implements. The Python function
`decide_verdict` mirrors `MemoryTest.verdict` below; the theorems state
what a "passing" run guarantees and what the gate detects.

Measurement model: a scenario runs `n` measured iterations. `leaks --diffFrom`
against one fixed post-warmup baseline graph is run at the checkpoint
(`iterations / 2`) and at the end, giving `firstHalf` (new leak roots seen at
the checkpoint) and `secondHalf` (the additional new roots between checkpoint
and end); `total` is the full reading at the end. A recurring leak fires in
both halves; a one-off leak fires in at most one. `parseOK` is false when a
`leaks` run produced no parseable summary (instrument failure). `growth` is
the physical-footprint increase in bytes over the whole run, and `maxGrowth`
is the total budget for the run (the runner computes it as its per-iteration
budget times the iteration count, which keeps this model linear).

Proved here (see the theorems at the bottom):

* An unparseable `leaks` reading can never yield a passing verdict
  (`fail_on_parse_failure`, `pass_soundness`) -- no silent false greens.
* Any leak that fires in both halves fails the scenario
  (`both_halves_fail`), so a leak recurring at least once per half-run is
  always detected, no matter how small the per-iteration count
  (`fired_every_window`).
* A leak that fires exactly once in the whole run can never fail the gate
  (`single_fire_not_fail`) -- one-off leaks are tolerated by design.
* The failing verdict is monotone in every counted axis (`fail_monotone`), so
  the blocks-instead-of-roots fallback (blocks >= roots) is conservative.
* The old yaview rule (`count >= 3 and count >= n/4`) provably never fails a
  leak that fires on every 5th iteration, at any iteration count
  (`old_rule_blind_spot`) -- the reason for the redesign.
-/

namespace MemoryTest

/-- Threshold configuration used by the runner. -/
structure Thresholds where
  /-- A one-off batch of new leaks at or above this fails the scenario. -/
  minLeaks : Nat
  /-- Total physical-footprint growth budget (bytes) for the whole run;
  the runner sets this to its per-iteration budget times the iterations. -/
  maxGrowth : Nat

/-- Runner defaults: 3 leak roots and 1 MiB of growth budget per iteration. -/
def defaultThresholds (iterations : Nat) : Thresholds :=
  ⟨3, 1048576 * iterations⟩

/-- One measured scenario run. -/
structure Measurement where
  /-- Every `leaks` reading produced a parseable summary. -/
  parseOK : Bool
  /-- New leak roots at the checkpoint, relative to the post-warmup baseline. -/
  firstHalf : Nat
  /-- New leak roots at the end, minus the checkpoint reading (floored at 0). -/
  secondHalf : Nat
  /-- New leak roots at the end, relative to the post-warmup baseline. -/
  total : Nat
  /-- Total physical-footprint growth (bytes) over the run. -/
  growth : Nat
  /-- Number of measured iterations (documentation only; the budget above is
  already total for the run). -/
  iterations : Nat

/-- Verdict of one scenario: pass, pass-with-one-off-leaks, or fail. -/
inductive Status where
  | ok
  | oneOff
  | fail

/-- The failure predicate: `verdict` fails exactly when this holds. Abbrev so
that the `if failing t m` in `verdict` can synthesize its `Decidable`
instance. -/
abbrev failing (t : Thresholds) (m : Measurement) : Prop :=
  m.parseOK = false
  ∨ (m.firstHalf ≥ 1 ∧ m.secondHalf ≥ 1)
  ∨ m.total ≥ t.minLeaks
  ∨ m.growth > t.maxGrowth

/-- Verdict of one scenario: pass, pass-with-one-off-leaks, or fail.
`decide_verdict` in memory_leak_tests.py mirrors this. -/
def verdict (t : Thresholds) (m : Measurement) : Status :=
  if failing t m then
    Status.fail
  else if m.total > 0 then
    Status.oneOff
  else
    Status.ok

/-- Exact characterization of when a scenario fails. -/
theorem fail_iff (t : Thresholds) (m : Measurement) :
    verdict t m = Status.fail ↔ failing t m := by
  unfold verdict failing
  split
  · rename_i hf
    simp [hf]
  · rename_i hf
    constructor
    · intro h
      split at h
      · simp at h
      · simp at h
    · intro hfail
      exact absurd hfail hf

/-- An unparseable `leaks` reading always fails: no silent false greens. -/
theorem fail_on_parse_failure (t : Thresholds) (m : Measurement)
    (h : m.parseOK = false) :
    verdict t m = Status.fail := by
  rw [fail_iff]
  exact Or.inl h

/-- A leak firing in both halves always fails. -/
theorem fail_on_recurring (t : Thresholds) (m : Measurement)
    (h1 : m.firstHalf ≥ 1) (h2 : m.secondHalf ≥ 1) :
    verdict t m = Status.fail := by
  rw [fail_iff]
  exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- A one-off batch at or above the threshold always fails. -/
theorem fail_on_batch (t : Thresholds) (m : Measurement)
    (h : m.total ≥ t.minLeaks) :
    verdict t m = Status.fail := by
  rw [fail_iff]
  exact Or.inr (Or.inr (Or.inl h))

/-- Footprint growth over budget always fails. -/
theorem fail_on_growth (t : Thresholds) (m : Measurement)
    (h : m.growth > t.maxGrowth) :
    verdict t m = Status.fail := by
  rw [fail_iff]
  exact Or.inr (Or.inr (Or.inr h))

/-- Master soundness: what a non-failing verdict guarantees. -/
theorem pass_soundness (t : Thresholds) (m : Measurement)
    (h : ¬ (verdict t m = Status.fail)) :
    m.parseOK = true
    ∧ (m.firstHalf = 0 ∨ m.secondHalf = 0)
    ∧ m.total < t.minLeaks
    ∧ m.growth ≤ t.maxGrowth := by
  have hnf : ¬ failing t m := fun hf => h (fail_iff t m |>.mpr hf)
  have h1 : ¬ (m.parseOK = false) := fun hh => hnf (Or.inl hh)
  have h2 : ¬ (m.firstHalf ≥ 1 ∧ m.secondHalf ≥ 1) :=
    fun hh => hnf (Or.inr (Or.inl hh))
  have h3 : ¬ (m.total ≥ t.minLeaks) := fun hh => hnf (Or.inr (Or.inr (Or.inl hh)))
  have h4 : ¬ (m.growth > t.maxGrowth) := fun hh => hnf (Or.inr (Or.inr (Or.inr hh)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hb : m.parseOK
    · exact absurd hb h1
    · rfl
  · by_cases hd1 : m.firstHalf ≥ 1
    · refine Or.inr ?_
      by_cases hd2 : m.secondHalf ≥ 1
      · exact absurd ⟨hd1, hd2⟩ h2
      · omega
    · exact Or.inl (by omega)
  · omega
  · omega

/-- The failing verdict is upward closed in every counted axis, so the
blocks-instead-of-roots fallback (blocks >= roots) is conservative. -/
theorem fail_monotone (t : Thresholds) (m m' : Measurement)
    (hp : m.parseOK = true)
    (hd1 : m'.firstHalf ≥ m.firstHalf) (hd2 : m'.secondHalf ≥ m.secondHalf)
    (hdt : m'.total ≥ m.total) (hdg : m'.growth ≥ m.growth)
    (h : verdict t m = Status.fail) :
    verdict t m' = Status.fail := by
  rw [fail_iff] at h
  rw [fail_iff]
  rcases h with hparse | hrec | hbatch | hgrowth
  · rw [hp] at hparse
    simp at hparse
  · refine Or.inr (Or.inl ?_)
    rcases hrec with ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-!
## Firing model

`fires i` says whether iteration `i` of the scenario leaked (allocated memory
that stays unreachable). The runner observes cumulative counts; the lemmas
below connect "fires in both halves" to the measured deltas.
-/

/-- Number of firing iterations among the first `k` iterations. -/
def countFires (fires : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => countFires fires k + (if fires k then 1 else 0)

/-- Number of firing iterations among `[start, start + k)`. -/
def countFiresFrom (fires : Nat → Bool) (start : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => countFiresFrom fires start k + (if fires (start + k) then 1 else 0)

theorem countFires_split (fires : Nat → Bool) (h w : Nat) :
    countFires fires (h + w) = countFires fires h + countFiresFrom fires h w := by
  induction w generalizing h with
  | zero => simp [countFiresFrom]
  | succ w ih =>
    by_cases hb : fires (h + w) = true
    · simp [countFires, countFiresFrom, ih, hb]
      omega
    · simp [countFires, countFiresFrom, ih, hb]

theorem countFires_ge_one {fires : Nat → Bool} {k : Nat}
    (h : ∃ j, j < k ∧ fires j = true) :
    countFires fires k ≥ 1 := by
  rcases h with ⟨j, hjk, hjf⟩
  induction k generalizing j with
  | zero => simp only [countFires]; omega
  | succ k ih =>
    cases Nat.lt_or_ge j k with
    | inl hlt =>
      have hIH := ih j hlt hjf
      cases hb : fires k
      · simp [countFires, hb] <;> omega
      · simp [countFires, hb] <;> omega
    | inr hge =>
      have hjk' : j = k := by omega
      subst hjk'
      simp [countFires, hjf] <;> omega

theorem countFiresFrom_ge_one {fires : Nat → Bool} {start k : Nat}
    (h : ∃ j, j < k ∧ fires (start + j) = true) :
    countFiresFrom fires start k ≥ 1 := by
  rcases h with ⟨j, hjk, hjf⟩
  induction k generalizing j with
  | zero => simp only [countFiresFrom]; omega
  | succ k ih =>
    cases Nat.lt_or_ge j k with
    | inl hlt =>
      have hIH := ih j hlt hjf
      cases hb : fires (start + k)
      · simp [countFiresFrom, hb] <;> omega
      · simp [countFiresFrom, hb] <;> omega
    | inr hge =>
      have hjk' : j = k := by omega
      subst hjk'
      simp [countFiresFrom, hjf] <;> omega

/-- Any leak firing at least once in each half of the run fails the gate,
regardless of parseOK (a parse failure fails the scenario on its own). -/
theorem both_halves_fail (t : Thresholds) (m : Measurement)
    (fires : Nat → Bool) (half : Nat)
    (h1 : m.firstHalf = countFires fires half)
    (h2 : m.secondHalf = countFiresFrom fires half half)
    (hf1 : countFires fires half ≥ 1)
    (hf2 : countFiresFrom fires half half ≥ 1) :
    verdict t m = Status.fail := by
  have hrec : m.firstHalf ≥ 1 ∧ m.secondHalf ≥ 1 := by
    rw [h1, h2]
    exact ⟨hf1, hf2⟩
  exact fail_on_recurring t m hrec.1 hrec.2

/-- If a leak fires in every window of `half` consecutive iterations, the
gate fails: instantiate the hypothesis at `a = 0` and `a = half`. -/
theorem fired_every_window (t : Thresholds) (m : Measurement)
    (fires : Nat → Bool) (half : Nat)
    (h1 : m.firstHalf = countFires fires half)
    (h2 : m.secondHalf = countFiresFrom fires half half)
    (hall : ∀ a, countFiresFrom fires a half ≥ 1) :
    verdict t m = Status.fail := by
  have hsplit := countFires_split fires 0 half
  simp [countFires] at hsplit
  have hf1 : countFires fires half ≥ 1 := by
    rw [hsplit]
    exact hall 0
  exact both_halves_fail t m fires half h1 h2 hf1 (hall half)

/-- A leak firing exactly once in the whole run can never fail the gate. -/
theorem single_fire_not_fail (t : Thresholds) (m : Measurement)
    (fires : Nat → Bool) (half : Nat)
    (hok : m.parseOK = true)
    (h1 : m.firstHalf = countFires fires half)
    (h2 : m.secondHalf = countFiresFrom fires half half)
    (hsum : countFires fires half + countFiresFrom fires half half = 1)
    (hbatch : m.total < t.minLeaks)
    (hgrowth : m.growth ≤ t.maxGrowth) :
    ¬ (verdict t m = Status.fail) := by
  intro hfail
  rw [fail_iff] at hfail
  rcases hfail with hparse | hrec | hbatch' | hgrowth'
  · rw [hok] at hparse
    simp at hparse
  · rcases hrec with ⟨hd1, hd2⟩
    rw [h1] at hd1
    rw [h2] at hd2
    omega
  · omega
  · omega

/-!
## The old yaview rule's blind spot

yaview failed a scenario only when `newLeaks >= max(3, iterations / 4)`.
Under cumulative leak count `n / 5` (a leak on every 5th iteration), that
condition is false at *every* iteration count: such a leak never fails the
old gate. The new rule fires on any leak that recurs within a half-run.
-/

/-- The old yaview verdict rule, on cumulative new-leak count and iteration count.
Python's `iterations / 4` is float division, so the rate conjunct is
formalized over the naturals as `count * 4 >= n`. -/
def oldFail (count n : Nat) : Prop := count ≥ 3 ∧ count * 4 ≥ n

theorem old_rule_blind_spot (n : Nat) : ¬ oldFail (n / 5) n := by
  unfold oldFail
  omega

end MemoryTest
