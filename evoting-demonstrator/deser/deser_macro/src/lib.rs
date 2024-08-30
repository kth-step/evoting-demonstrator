use proc_macro::TokenStream;
use quote::{format_ident, quote};

#[proc_macro_derive(Serialise)]
pub fn serialise_macro_derive(tokens: TokenStream) -> TokenStream {
    // converts tokens into an Enum AST
    let ast: syn::ItemEnum = syn::parse(tokens).unwrap();

    let enum_name = ast.ident;

    let constrs = ast.variants.iter();
    let mut matches = Vec::new();

    for (k,constr) in constrs.enumerate() {

        let k = k as u8;
        let variant_name = &constr.ident;

        if 0 < constr.fields.len() {
            // loop over constructor attributes
            let field_name: Vec<_> = constr.fields.iter().enumerate().map(|(i, _)| {
                let f = format_ident!("x{}", i); // , f.type)
                quote!(#f)
            }).collect();

            let q = quote!{
                #enum_name::#variant_name (#(#field_name,)*) => {
                    let mut result : Vec<Vec<u8>> = Vec::new();
                    result.push(vec![#k]);
                    #(
                        let Some(b) = #field_name.serialise() else {
                            // return None;
                            panic!("Serialise: cannot serialise field {} of {}::{}", stringify!(#field_name), stringify!(#enum_name), stringify!(#variant_name));
                        };
                        result.push(b);
                    )*
                    return Some (result.concat())
                }
            };
            // println!("multiple:\n{}", q);
            matches.push(q);
        } else {
            let q = quote!{
                #enum_name::#variant_name => Some(vec![#k])
            };
            // println!("single:\n{}", q);
            matches.push(q);
        }
    }

    let q = quote!{
        impl Serialise for #enum_name {
            fn serialise(self : #enum_name) -> Option <Vec<u8>> {
                match self {
                #(#matches,)*
                    _ => None,
                }
            }
        }
    };

    // panic!("My struct name is: <{}>", ast.ident.to_string());
    // TokenStream::new()
    q.into()
}

#[proc_macro_derive(Deserialise)]
pub fn deserialise_macro_derive(tokens: TokenStream) -> TokenStream {
    // converts tokens into an Enum AST
    let ast: syn::ItemEnum = syn::parse(tokens).unwrap();

    let enum_name = ast.ident;

    let constrs = ast.variants.iter();
    let mut matches = Vec::new();

    for (k,constr) in constrs.enumerate() {

        let k = k as u8;
        let variant_name = &constr.ident;

        let field_no = constr.fields.len();
        if 0 < field_no {
            // deserialise each argument
            let mut arg_q = Vec::with_capacity(field_no);
            for (i,arg) in constr.fields.iter().enumerate() {
              let typ = &arg.ty;
                // println!("i {} ty: {}", i, quote!{#typ :: serialise() });
                let q = if i == 0 {
                    quote!{ <#typ>::deserialise(&buf[1..].to_vec()) }
                } else {
                    // sum up all previous offsets
                    let index_str_pre = arg_q.iter().map(|(_,i,_)| i);
                    quote!{ <#typ>::deserialise(&buf[(1 #(+ #index_str_pre)*) ..].to_vec()) }
                };
                // argname argterm
                arg_q.push((format_ident!("x{}",i), format_ident!("i{}",i), q));
            }
            let arg_str_pre = arg_q.iter().map(|(x,_,_)| x);
            let index_str_pre = arg_q.iter().map(|(_,i,_)| i);
            let fin_term = arg_q.iter().rev().fold(
                quote!{
                    Some ((#enum_name::#variant_name (#(#arg_str_pre,)*) ,
                        1 #(+ #index_str_pre)* ))
                    },
                    |acc , (x,i,tm)| quote!{ #tm.and_then(|(#x,#i)| #acc) }
                );
            let q = quote!{
                #k => #fin_term
            };
            // println!("multiple:\n{}", q);
            matches.push(q);
        } else {
            let q = quote!{
                #k => Some((#enum_name::#variant_name, 1))
            };
            // println!("single:\n{}", q);
            matches.push(q);
        }
    }

    let q = quote!{
        impl Deserialise for #enum_name {
            fn deserialise(buf : &[u8]) -> Option <(#enum_name, usize)> {
                if buf.is_empty() { return None }
                match buf[0] {
                #(#matches,)*
                    _ => None,
                }
            }
        }
    };

    // panic!("My struct name is: <{}>", ast.ident.to_string());
    // TokenStream::new()
    q.into()
}


