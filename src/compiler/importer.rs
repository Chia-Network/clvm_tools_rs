// An import system for chialisp.
//
// Scheme:
//
// - Imported files appear logically before included files.
// - Files are located by assuming that (.) characters terminate the names of
//   path components and look for .clib or .clinc files on the filesystem in
//   each of the include locations after forming the full path.
//
// The general procedure for reading imports is that we first collect all files
// referenced by imports in any file where they occur.  The import toplevel
// form doesn't have any effect after reading so we remove it from the stored
// versions.  We record any imports and the hash of any file we read via import,
// and store them in a two stage index, first by import spec to hash and then
// hash to content.
//
// We toposort the imports by their dependencies into an ordered list of hashes,
// then create a single synthetic include file for the program from their content
// by renaming each helperform to its fully qualified name.
//
// We need the name resolution to work differently in each imported module, so
// we support a "defalias" element at the top level and we emit defalias elements
// for each input form that is affected by import along with an unique identifer.
// aliases that are identified can be withdrawn so we emit withdrawing defalias
// elements after the forms for which the defalias forms apply.
//
// Example:
//
// a/foo.clib
//
//   (
//     (import a.bar) ;; exposes YConstant
//     (import qualified a.pkg.more) ;; exposes a.pkg.more.doit
//
//     (defconst XConstant YConstant)
//     (defconst MoreConstant (a.pkg.more.doit YConstant)
//   )
//
// a/pkg/more.clib
//
//   (
//     (import a.foo) ;; exposes XConstant and MoreConstant
//
//     (defun doit (X) (+ X XConstant))
//   )
//
// a/bar.clib
//
//   (
//     (defconst YConstant 99)
//   )
//

#[derive(Clone, Default, Debug, PartialEq, Eq, Ord, Hash)]
pub struct NameSegment {
    value: Vec<u8>,
}

#[derive(Clone, Default, Debug, PartialEq, Eq, Ord, Hash)]
pub struct ImportDescription {
    name_chain: Vec<NameSegment>,
}

///
/// ImportTransformer takes the SExp contents of a chialisp program containing
/// import forms and rewrites it with include forms.
///
/// The emitted chialisp program contains extra forms that manage
///
#[derive(Debug)]
pub struct ImportTransformer {
    known_modules: HashMap<ImportDescription, ImportedFile>,
}

