// TODO: pub(crate) ?
pub type CRef = u32;
pub const HEADER_LEN: usize = 2;

// Glucose representation of a Clause
/*
class Clause {
    struct {
        unsigned mark : 2;
        unsigned learnt : 1;
        unsigned has_extra : 1;
        unsigned reloced : 1;
        unsigned canbedel : 1;
        unsigned location : 2;
        unsigned simplified : 1;
        unsigned exported : 2;
        unsigned lbd : 21;
        unsigned imported : 1;
        unsigned oneWatched : 1;
        unsigned size : 30;
    } header;
    union {
        Lit      lit;
        float    act;
        uint32_t abs;
        uint32_t touched;
        CRef     rel;
    } data[0];
}
*/

/*
How about this:
[search: 8, other: 8, lbd: 16]
For JigSAT I need:
size (clause length) : 30 or 32 bits. Easiest is just to have first header be clause length
lbd : up to 21 bits. The lbd is just a heuristic, so it can be reduced in size. Will most likely be "the rest of the bits" ("bottom shave" or "top shave"?).
search : 8 to 10 bits ? 8 bits = 256 possible values, 10 bits = 1024 possible values. Just a heuristic, so it is not an issue that search sucks for large clauses.
can_be_del : 1 bit

unsigned canbedel : 1;


// Unsure whether I need:
// What is the mark needed for again? Need to check.
// It seems to be used both to indicate deleted (mark 1) and to indicate clause location (when using the tiered clause manager)
// Should be possible to get away with having a deleted field, and then optionally adding a second mark field later.
unsigned mark : 2;
// If we know the cref, we know whether it is learnt. 1 bit.
unsigned learnt : 1;
// Needed if we open to having a clause tail. 1 bit.
unsigned has_extra : 1;
// Unsure why this is needed. Need to check. 1 bit.
unsigned reloced : 1;
// Dunno what the gain is in having this. A bit cumbersome to maintain the invariant that the location is correct.
// Either 2 bits or 1 bit if we use learnt or cref < original.len() and then discriminate on this afterwards
unsigned location : 2;
// Why is this needed? Need to check. 1 bit.
unsigned simplified : 1;

// Unsure about these three.
unsigned exported : 2;
unsigned imported : 1;
unsigned oneWatched : 1;
*/