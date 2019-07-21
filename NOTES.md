# Notes

As it stands, PartialSetoids (and by extension, algebraic structures)
are parameterized by their carrier type.
This is a bit awkward, as it doesn't line up with
the rest of the definitions in the stdlib, which pack
away their carrier type inside of a record.

The reason we have to parameterize is because of subsets (and submonoids,
subgroups, etc). We need to ensure that they are defined over the same carrier
type, wich would be very difficult to do if we pack away the carrier type.

The only way around this issue (that I can see) is to parameterize the
subset relations with a type equality over the carrier types, but this seems
not _super_ great.

