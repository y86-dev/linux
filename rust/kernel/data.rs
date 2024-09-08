use core::ops::Deref;

/// A piece of untrusted data.
#[repr(transparent)]
pub struct Untrusted<T: ?Sized>(T);

impl<T: ?Sized> Untrusted<T> {
    /// Marks the value as untrusted.
    pub fn new_untrusted(value: T) -> Self
    where
        T: Sized,
    {
        Self(value)
    }

    /// Marks the value behind the reference as untrusted.
    pub fn new_untrusted_ref<'a>(value: &'a T) -> &'a Self {
        let ptr: *const T = value;
        // CAST: `Self` is `repr(transparent)` and contains a `T`.
        let ptr = ptr as *const Self;
        // SAFETY: `ptr` came from a shared reference valid for `'a`.
        unsafe { &*ptr }
    }

    /// Gives access to the underlying untrusted data.
    ///
    /// Be careful when accessing the data, as it is untrusted and still needs to be verified. To
    /// do so use [`validate`].
    pub fn untrusted(&self) -> &T {
        &self.0
    }

    ///
    pub fn deref(&self) -> &Untrusted<<T as Deref>::Target>
    where
        T: Deref,
    {
        Untrusted::new_untrusted_ref(self.0.deref())
    }

    /// Validates the untrusted data.
    pub fn validate<V: Validator<Input = T>>(&self) -> Result<V::Output, V::Err> {
        V::validate(self)
    }
}

impl<T> Untrusted<[T]> {
    pub fn subslice(&self, offset: usize, len: usize) -> &Self {
        Self::new_untrusted_ref(&self.0[offset..][..len])
    }

    pub fn len(&self) -> usize {
        self.len()
    }
}

/// Validates untrusted data.
///
/// # Examples
///
/// ## Using an API returning untrusted data
///
/// Create the type of the data that you want to parse:
///
/// ```
/// pub struct FooData {
///     data: [u8; 4],
/// }
/// ```
///
/// Then impement this trait:
///
/// ```
/// impl Validator for FooData {
///     type Input = [u8];
///     type Output = FooData;
///     type Err = Error;
///
///     fn validate(untrusted: &Untrusted<Self::Input>) -> Result<Self::Output, Self::Err> {
///         let untrusted = untrusted.untrusted();
///         let untrusted = <[u8; 4]>::try_from(untrusted);
///         for byte in &untrusted {
///             if byte & 0xf0 != 0 {
///                 return Err(());
///             }
///         }
///         Ok(FooData { data: untrusted })
///     }
/// }
/// ```
///
/// And then use the API that returns untrusted data:
///
/// ```
/// let result = foo.get_untrusted_data().validate::<FooData>();
/// ```
///
/// ## Creating an API returning untrusted data
///
/// In your API instead of just returning the untrusted data, wrap it in [`Untrusted<T>`]:
///
/// ```
/// pub fn get_untrusted_data(&self) -> &Untrusted<[u8]>;
/// ```
///
pub trait Validator {
    type Input: ?Sized;
    /// Type of the validated data.
    type Output;
    type Err;

    fn validate(untrusted: &Untrusted<Self::Input>) -> Result<Self::Output, Self::Err>;
}
