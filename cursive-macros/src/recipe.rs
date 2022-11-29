use proc_macro::TokenStream;
use quote::quote;

pub fn recipe(item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::ImplItemMethod);

    TokenStream::from(quote! {
        #[allow(dead_code)]
        #input
    })
}
