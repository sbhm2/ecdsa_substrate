// For better debugging (printout) support
use core::{convert::TryInto};
use sp_std::{prelude::*, str, collections::vec_deque::VecDeque};
use frame_support::{ debug ,decl_module, decl_storage, decl_error, dispatch::DispatchResult};
use frame_system:: {ensure_signed, ensure_none,
  offchain::{
    AppCrypto, CreateSignedTransaction, SendSignedTransaction, SendUnsignedTransaction, Signer, SubmitTransaction,
    SignedPayload, SigningTypes,
  },
};
use codec::{Decode, Encode};

use sp_runtime::{
  RuntimeDebug,
  offchain::{self as rt_offchain, http,
		// storage::StorageValueRef,
		// storage_lock::{StorageLock, BlockAndTime},
	},
  transaction_validity::{
    ValidTransaction, TransactionValidity, InvalidTransaction, TransactionSource
  }
};
use sp_std::vec::Vec;
use sp_core::crypto::KeyTypeId;

use alt_serde::{Deserialize, Deserializer};
use serde_json::{Value};

// use sp_runtime::transaction_validity::{
//   TransactionValidity, TransactionLongevity, ValidTransaction, InvalidTransaction
// };
// The key type ID can be any 4-character string
// pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"abcd");

// --snip--

// pub mod crypto {
//   pub use super::KEY_TYPE;
//   use sp_runtime::app_crypto::{app_crypto, sr25519};
//   app_crypto!(sr25519, KEY_TYPE);
// }

pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"demo");
pub const NUM_VEC_LEN: usize = 10;
/// The type to sign and send transactions.
pub const UNSIGNED_TXS_PRIORITY: u64 = 100;

pub const HTTP_REMOTE_REQUEST: &str = "https://run.mocky.io/v3/2996fed9-695f-4a65-814e-5f6ae0915114";
pub const FETCH_TIMEOUT_PERIOD: u64 = 3000; // in milli-seconds
pub const LOCK_TIMEOUT_EXPIRATION: u64 = FETCH_TIMEOUT_PERIOD + 1000; // in milli-seconds
pub const LOCK_BLOCK_EXPIRATION: u32 = 3; // in block number
// pub const DEVEUI: T::Hash = "00800000040163e3";

pub mod crypto {
    pub use super::KEY_TYPE;
    use sp_core::ecdsa::Signature as EcdsaSignature;
    use sp_runtime::app_crypto::{app_crypto, ecdsa};
    use sp_runtime::{
      traits::Verify,
		  MultiSignature, MultiSigner,
    };
    // -- snip --
    app_crypto!(ecdsa, KEY_TYPE);

    pub struct TestAuthId;
    impl frame_system::offchain::AppCrypto<MultiSigner, MultiSignature> for TestAuthId {
      type RuntimeAppPublic = Public;
      type GenericSignature = sp_core::ecdsa::Signature;
      type GenericPublic = sp_core::ecdsa::Public;
    }
  
    // implemented for mock runtime in test
    impl frame_system::offchain::AppCrypto<<EcdsaSignature as Verify>::Signer, EcdsaSignature>
      for TestAuthId
    {
      type RuntimeAppPublic = Public;
      type GenericSignature = sp_core::ecdsa::Signature;
      type GenericPublic = sp_core::ecdsa::Public;
    }
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Payload<Public> {
	number: u64,
	public: Public
}

impl <T: SigningTypes> SignedPayload<T> for Payload<T::Public> {
	fn public(&self) -> T::Public {
		self.public.clone()
	}
}

// Specifying serde path as `alt_serde`
// ref: https://serde.rs/container-attrs.html#crate
#[serde(crate = "alt_serde")]
#[derive(Deserialize, Encode, Decode, Default)]
struct NodeStatus {
	// Specify our own deserializing function to convert JSON string to vector of bytes
	// #[serde(deserialize_with = "de_string_to_bytes")]
	presence: bool,
	// #[serde(deserialize_with = "de_string_to_bytes")]
	// blog: Vec<u8>,
	// public_repos: u32,
}

pub trait Trait: frame_system::Trait + CreateSignedTransaction<Call<Self>> {
   // The overarching event type.
   type AuthorityId: AppCrypto<Self::Public, Self::Signature>;
  }

  decl_storage! {
    trait Store for Module<T: Trait> as Example {
      /// A vector of recently submitted numbers. Bounded by NUM_VEC_LEN
      Numbers get(fn numbers): VecDeque<u64>;
    }
  }

  decl_error! {
    pub enum Error for Module<T: Trait> {
      // Error returned when not sure which ocw function to executed
      NoNeedToCheck,
  
      // Error returned when making signed transactions in off-chain worker
      NoLocalAcctForSigning,
      OffchainSignedTxError,
  
      // Error returned when making unsigned transactions in off-chain worker
      OffchainUnsignedTxError,
  
      // Error returned when making unsigned transactions with signed payloads in off-chain worker
      OffchainUnsignedTxSignedPayloadError,
  
      // Error returned when fetching github info
      HttpFetchingError,
    }
  }

  decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
      // fn deposit_event() = default;
      // --snip--

      #[weight = 10000]
		pub fn submit_number_signed(origin, number: u64, status: bool, deveui: Vec<u8>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			debug::info!("submit_number_signed: ({}, {:?})", number, who);
      Self::append_or_replace_number(number);
			Ok(())
    }
    
    
    #[weight = 10000]
		pub fn submit_number_unsigned(origin, number: u64) -> DispatchResult {
			let _ = ensure_none(origin)?;
			debug::info!("submit_number_unsigned: {}", number);
			Self::append_or_replace_number(number);

			Ok(())
    }
    
    #[weight = 10000]
		pub fn submit_number_unsigned_with_signed_payload(origin, payload: Payload<T::Public>,
			_signature: T::Signature) -> DispatchResult
		{
			let _ = ensure_none(origin)?;
			// we don't need to verify the signature here because it has been verified in
			//   `validate_unsigned` function when sending out the unsigned tx.
			let Payload { number, public } = payload;
			debug::info!("submit_number_unsigned_with_signed_payload: ({}, {:?})", number, public);
			Self::append_or_replace_number(number);

			Ok(())
		}
  
    fn offchain_worker(block_number: T::BlockNumber) {
      
      debug::info!("Hello World.");
      const TRANSACTION_TYPES: usize = 3;

        let result = match block_number.try_into()
          .map_or(TRANSACTION_TYPES, |bn| bn % TRANSACTION_TYPES)
        {
          0 => Self::fetch_n_parse(),
          _ => Err(Error::<T>::NoNeedToCheck),
        };
      }
    }
  }
  
impl<T: Trait> Module<T> {
  fn u32_to_blocknumber(input: u32) -> T::BlockNumber {
    input.into()
  }

  // pub fn ordered_trie_root(input: Vec<Vec<u8>>) -> Self::Output {
  //   input.into()
  // }

  /// Fetch from remote and deserialize the JSON to a struct
  fn fetch_n_parse() -> Result<serde_json::Value, Error<T>> {
    let resp_bytes = Self::fetch_from_remote().map_err(|e| {
      debug::error!("fetch_from_remote error: {:?}", e);
      <Error<T>>::HttpFetchingError
    })?;

    let resp_str = str::from_utf8(&resp_bytes).map_err(|_| <Error<T>>::HttpFetchingError)?;
    // Print out our fetched JSON string
    debug::info!("{}", resp_str);

    // Deserializing JSON to struct, thanks to `serde` and `serde_derive`
    let node_info: Value =
      serde_json::from_str(&resp_str).map_err(|_| <Error<T>>::HttpFetchingError)?;

    let src: &str = r#"00800000040163e3"#;
    // let hashed = Self.ordered_trie_root(byte4);
    if node_info["presence"] == false {
      // let node_status = NodeStatus { presence: false};
      let not_present: u32 = 0;
      let not_present_in_block = Self::u32_to_blocknumber(not_present);
      Self::offchain_signed_tx(not_present_in_block, false, src);
    }
    else{
      let present: u32 = 1;
      let present_in_block = Self::u32_to_blocknumber(present);
      Self::offchain_signed_tx(present_in_block, true, src);
    }
    // {NodeStatus presence:node_info["presence"]};
    Ok(node_info)
  }

  /// This function uses the `offchain::http` API to query the remote github information,
  ///   and returns the JSON response as vector of bytes.
  fn fetch_from_remote() -> Result<Vec<u8>, Error<T>> {
    debug::info!("sending request to: {}", HTTP_REMOTE_REQUEST);

    // Initiate an external HTTP GET request. This is using high-level wrappers from `sp_runtime`.
    let request = rt_offchain::http::Request::get(HTTP_REMOTE_REQUEST);

    // Keeping the offchain worker execution time reasonable, so limiting the call to be within 3s.
    let timeout = sp_io::offchain::timestamp()
      .add(rt_offchain::Duration::from_millis(FETCH_TIMEOUT_PERIOD));

    // For github API request, we also need to specify `user-agent` in http request header.
    //   See: https://developer.github.com/v3/#user-agent-required
     // Specifying the request
     let pending = http::Request::get(HTTP_REMOTE_REQUEST)
     .send()
     .map_err(|_| <Error<T>>::HttpFetchingError)?;

    // By default, the http request is async from the runtime perspective. So we are asking the
    //   runtime to wait here.
    // The returning value here is a `Result` of `Result`, so we are unwrapping it twice by two `?`
    //   ref: https://substrate.dev/rustdocs/v2.0.0/sp_runtime/offchain/http/struct.PendingRequest.html#method.try_wait
    let response = pending
      .try_wait(timeout)
      .map_err(|_| <Error<T>>::HttpFetchingError)?
      .map_err(|_| <Error<T>>::HttpFetchingError)?;

    if response.code != 200 {
      debug::error!("Unexpected http request status code: {}", response.code);
      return Err(<Error<T>>::HttpFetchingError);
    }

    // Next we fully read the response body and collect it to a vector of bytes.
    Ok(response.body().collect::<Vec<u8>>())
  }

  fn append_or_replace_number(number: u64) {
		Numbers::mutate(|numbers| {
			if numbers.len() == NUM_VEC_LEN {
				let _ = numbers.pop_front();
			}
			numbers.push_back(number);
			debug::info!("Number vector: {:?}", numbers);
		});
	}

	fn offchain_unsigned_tx_signed_payload(block_number: T::BlockNumber) -> Result<(), Error<T>> {
		// Retrieve the signer to sign the payload
		let signer = Signer::<T, T::AuthorityId>::any_account();

		let number: u64 = block_number.try_into().unwrap_or(0) as u64;

		// `send_unsigned_transaction` is returning a type of `Option<(Account<T>, Result<(), ()>)>`.
		//   Similar to `send_signed_transaction`, they account for:
		//   - `None`: no account is available for sending transaction
		//   - `Some((account, Ok(())))`: transaction is successfully sent
		//   - `Some((account, Err(())))`: error occured when sending the transaction
		if let Some((_, res)) = signer.send_unsigned_transaction(
			|acct| Payload { number, public: acct.public.clone() },
			Call::submit_number_unsigned_with_signed_payload
		) {
			return res.map_err(|_| {
				debug::error!("Failed in offchain_unsigned_tx_signed_payload");
				<Error<T>>::OffchainUnsignedTxSignedPayloadError
			});
		}

		// The case of `None`: no account is available for sending
		debug::error!("No local account available");
		Err(<Error<T>>::NoLocalAcctForSigning)
	}

  fn offchain_unsigned_tx(block_number: T::BlockNumber) -> Result<(), Error<T>> {
		let number: u64 = block_number.try_into().unwrap_or(0) as u64;
		let call = Call::submit_number_unsigned(number);

		// `submit_unsigned_transaction` returns a type of `Result<(), ()>`
		//   ref: https://substrate.dev/rustdocs/v2.0.0/frame_system/offchain/struct.SubmitTransaction.html#method.submit_unsigned_transaction
		SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into())
			.map_err(|_| {
				debug::error!("Failed in offchain_unsigned_tx");
				<Error<T>>::OffchainUnsignedTxError
			})
	}


fn offchain_signed_tx(block_number: T::BlockNumber, status: bool, src: &str) -> Result<(), Error<T>> {
  // We retrieve a signer and check if it is valid.
  //   Since this pallet only has one key in the keystore. We use `any_account()1 to
  //   retrieve it. If there are multiple keys and we want to pinpoint it, `with_filter()` can be chained,
  //   ref: https://substrate.dev/rustdocs/v2.0.0/frame_system/offchain/struct.Signer.html

  let byte4: Vec<u8> = src.as_bytes().to_vec();

  let signer = Signer::<T, T::AuthorityId>::any_account();

  // Translating the current block number to number and submit it on-chain
  let number: u64 = block_number.try_into().unwrap_or(0) as u64;

  // `result` is in the type of `Option<(Account<T>, Result<(), ()>)>`. It is:
  //   - `None`: no account is available for sending transaction
  //   - `Some((account, Err(())))`: error occured when sending the transaction
  //   - `Some((account, Ok(())))`: transaction is successfully sent
  let result = signer.send_signed_transaction(|_acct|
      // This is the on-chain function
      Call::submit_number_signed(number, status, byte4.clone())
  );

  // Display error if the signed tx fails.
  if let Some((acc, res)) = result {
      if res.is_err() {
          debug::error!("failure: offchain_signed_tx: tx sent: {:?}", acc.id);
          return Err(<Error<T>>::OffchainSignedTxError);
      }
      // Transaction is sent successfully
      return Ok(());
  }

  // The case of `None`: no account is available for sending
  debug::error!("No local account available");
  Err(<Error<T>>::NoLocalAcctForSigning)
}
}

//Implemention to allow unsigned transaction in chain
impl<T: Trait> frame_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;

	fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
		let valid_tx = |provide| ValidTransaction::with_tag_prefix("ocw-demo")
			.priority(UNSIGNED_TXS_PRIORITY)
			.and_provides([&provide])
			.longevity(3)
			.propagate(true)
			.build();

		match call {
			Call::submit_number_unsigned(_number) => valid_tx(b"submit_number_unsigned".to_vec()),
			Call::submit_number_unsigned_with_signed_payload(ref payload, ref signature) => {
				if !SignedPayload::<T>::verify::<T::AuthorityId>(payload, signature.clone()) {
					return InvalidTransaction::BadProof.into();
				}
				valid_tx(b"submit_number_unsigned_with_signed_payload".to_vec())
			},
			_ => InvalidTransaction::Call.into(),
		}
	}
}