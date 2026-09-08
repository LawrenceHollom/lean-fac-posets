import AharoniKorman.Completion.Accumulation
import AharoniKorman.Completion.Continuity
import AharoniKorman.Completion.CutRealization

/-! The frozen Phase E completion interface.

Later phases should import this module and use public representative, comparison,
embedding, bound, accumulation, and profile lemmas. See `COMPLETION_API.md` for the
assumptions and endpoint conventions. Germ setoids and quotient implementations are
not part of this interface.
-/
