/* globals RTCPeerConnection: false, RTCSessionDescription: false */

const EventEmitter = require('events').EventEmitter;
const JsSIP_C = require('./Constants');
const Exceptions = require('./Exceptions');
const Utils = require('./Utils');
const Timers = require('./Timers');
const SIPMessage = require('./SIPMessage');
const Dialog = require('./Dialog');
const RequestSender = require('./RequestSender');
const RTCSession_DTMF = require('./RTCSession/DTMF');
const RTCSession_Info = require('./RTCSession/Info');
const URI = require('./URI');
const debug = require('debug')('JsSIP:RTCSession');
const debugerror = require('debug')('JsSIP:ERROR:RTCSession');

debugerror.log = console.warn.bind(console);

const C = {
  // RTCSession states.
  STATUS_NULL               : 0,
  STATUS_INVITE_SENT        : 1,
  STATUS_1XX_RECEIVED       : 2,
  STATUS_INVITE_RECEIVED    : 3,
  STATUS_WAITING_FOR_ANSWER : 4,
  STATUS_ANSWERED           : 5,
  STATUS_WAITING_FOR_ACK    : 6,
  STATUS_CANCELED           : 7,
  STATUS_TERMINATED         : 8,
  STATUS_CONFIRMED          : 9
};

module.exports = class RTCSession extends EventEmitter
{
  /**
   * Expose C object.
   */
  static get C()
  {
    return C;
  }

  constructor(ua)
  {
    debug('new');

    super();

    this._id = null;
    this._ua = ua;
    this._status = C.STATUS_NULL;
    this._dialog = null;
    this._earlyDialogs = {};
    this._contact = null;
    this._from_tag = null;
    this._to_tag = null;

    // The RTCPeerConnection instance (public attribute).
    this._connection = null;

    // Prevent races on serial PeerConnction operations.
    this._connectionPromiseQueue = Promise.resolve();

    // Incoming/Outgoing request being currently processed.
    this._request = null;

    // Cancel state for initial outgoing request.
    this._is_canceled = false;
    this._cancel_reason = '';

    // RTCSession confirmation flag.
    this._is_confirmed = false;

    // Is late SDP being negotiated.
    this._late_sdp = false;

    // Default rtcOfferConstraints and rtcAnswerConstrainsts (passed in connect() or answer()).
    this._rtcOfferConstraints = null;
    this._rtcAnswerConstraints = null;

    // Flag to indicate PeerConnection ready for new actions.
    this._rtcReady = true;

    // SIP Timers.
    this._timers = {
      ackTimer          : null,
      expiresTimer      : null,
      invite2xxTimer    : null,
      userNoAnswerTimer : null
    };

    // Session info.
    this._direction = null;
    this._local_identity = null;
    this._remote_identity = null;
    this._start_time = null;
    this._end_time = null;
    this._tones = null;

    // Session Timers (RFC 4028).
    this._sessionTimers = {
      enabled        : this._ua.configuration.session_timers,
      refreshMethod  : this._ua.configuration.session_timers_refresh_method,
      defaultExpires : JsSIP_C.SESSION_EXPIRES,
      currentExpires : null,
      running        : false,
      refresher      : false,
      timer          : null // A setTimeout.
    };

    // Custom session empty object for high level use.
    this._data = {};
  }

  /**
   * User API
   */

  // Expose RTCSession constants as a property of the RTCSession instance.
  get C()
  {
    return C;
  }

  // Expose session failed/ended causes as a property of the RTCSession instance.
  get causes()
  {
    return JsSIP_C.causes;
  }

  get id()
  {
    return this._id;
  }

  get connection()
  {
    return this._connection;
  }

  get contact()
  {
    return this._contact;
  }

  get direction()
  {
    return this._direction;
  }

  get local_identity()
  {
    return this._local_identity;
  }

  get remote_identity()
  {
    return this._remote_identity;
  }

  get start_time()
  {
    return this._start_time;
  }

  get end_time()
  {
    return this._end_time;
  }

  get data()
  {
    return this._data;
  }

  set data(_data)
  {
    this._data = _data;
  }

  get status()
  {
    return this._status;
  }

  isInProgress()
  {
    switch (this._status)
    {
      case C.STATUS_NULL:
      case C.STATUS_INVITE_SENT:
      case C.STATUS_1XX_RECEIVED:
      case C.STATUS_INVITE_RECEIVED:
      case C.STATUS_WAITING_FOR_ANSWER:
        return true;
      default:
        return false;
    }
  }

  isEstablished()
  {
    switch (this._status)
    {
      case C.STATUS_ANSWERED:
      case C.STATUS_WAITING_FOR_ACK:
      case C.STATUS_CONFIRMED:
        return true;
      default:
        return false;
    }
  }

  isEnded()
  {
    switch (this._status)
    {
      case C.STATUS_CANCELED:
      case C.STATUS_TERMINATED:
        return true;
      default:
        return false;
    }
  }

  connect(target, sdp, options = {}, initCallback)
  {
    debug('connect()');

    const originalTarget = target;
    const eventHandlers = options.eventHandlers || {};
    const extraHeaders = Utils.cloneArray(options.extraHeaders);

    this._data = options.data || this._data;

    // Check target.
    if (target === undefined)
    {
      throw new TypeError('Not enough arguments');
    }

    // Check Session Status.
    if (this._status !== C.STATUS_NULL)
    {
      throw new Exceptions.InvalidStateError(this._status);
    }

    // Check target validity.
    target = this._ua.normalizeTarget(target);
    if (!target)
    {
      throw new TypeError(`Invalid target: ${originalTarget}`);
    }

    // Session Timers.
    if (this._sessionTimers.enabled)
    {
      if (Utils.isDecimal(options.sessionTimersExpires))
      {
        if (options.sessionTimersExpires >= JsSIP_C.MIN_SESSION_EXPIRES)
        {
          this._sessionTimers.defaultExpires = options.sessionTimersExpires;
        }
        else
        {
          this._sessionTimers.defaultExpires = JsSIP_C.SESSION_EXPIRES;
        }
      }
    }

    // Set event handlers.
    for (const event in eventHandlers)
    {
      if (Object.prototype.hasOwnProperty.call(eventHandlers, event))
      {
        this.on(event, eventHandlers[event]);
      }
    }

    // Session parameter initialization.
    this._from_tag = Utils.newTag();

    // Set anonymous property.
    const anonymous = options.anonymous || false;

    const requestParams = { from_tag: this._from_tag };

    this._contact = this._ua.contact.toString({
      anonymous,
      outbound : true
    });

    if (anonymous)
    {
      requestParams.from_display_name = 'Anonymous';
      requestParams.from_uri = new URI('sip', 'anonymous', 'anonymous.invalid');

      extraHeaders.push(`P-Preferred-Identity: ${this._ua.configuration.uri.toString()}`);
      extraHeaders.push('Privacy: id');
    }

    extraHeaders.push(`Contact: ${this._contact}`);
    extraHeaders.push('Content-Type: application/sdp');
    if (this._sessionTimers.enabled)
    {
      extraHeaders.push(`Session-Expires: ${this._sessionTimers.defaultExpires}`);
    }

    this._request = new SIPMessage.InitialOutgoingInviteRequest(
      target, this._ua, requestParams, extraHeaders);

    this._id = this._request.call_id + this._from_tag;

    // Set internal properties.
    this._direction = 'outgoing';
    this._local_identity = this._request.from;
    this._remote_identity = this._request.to;

    // User explicitly provided a newRTCSession callback for this session.
    if (initCallback)
    {
      initCallback(this);
    }

    this._newRTCSession('local', this._request);

    this._sendInitialRequest(sdp);
  }

  /**
   * Terminate the call.
   */
  terminate(options = {})
  {
    debug('terminate()');

    const cause = options.cause || JsSIP_C.causes.BYE;
    const extraHeaders = Utils.cloneArray(options.extraHeaders);
    const body = options.body;

    let cancel_reason;
    let status_code = options.status_code;
    let reason_phrase = options.reason_phrase;

    // Check Session Status.
    if (this._status === C.STATUS_TERMINATED)
    {
      throw new Exceptions.InvalidStateError(this._status);
    }

    switch (this._status)
    {
      // - UAC -
      case C.STATUS_NULL:
      case C.STATUS_INVITE_SENT:
      case C.STATUS_1XX_RECEIVED:
        debug('canceling session');

        if (status_code && (status_code < 200 || status_code >= 700))
        {
          throw new TypeError(`Invalid status_code: ${status_code}`);
        }
        else if (status_code)
        {
          reason_phrase = reason_phrase || JsSIP_C.REASON_PHRASE[status_code] || '';
          cancel_reason = `SIP ;cause=${status_code} ;text="${reason_phrase}"`;
        }

        // Check Session Status.
        if (this._status === C.STATUS_NULL || this._status === C.STATUS_INVITE_SENT)
        {
          this._is_canceled = true;
          this._cancel_reason = cancel_reason;
        }
        else if (this._status === C.STATUS_1XX_RECEIVED)
        {
          this._request.cancel(cancel_reason);
        }

        this._status = C.STATUS_CANCELED;

        this._failed('local', null, JsSIP_C.causes.CANCELED);
        break;

      case C.STATUS_WAITING_FOR_ACK:
      case C.STATUS_CONFIRMED:
        debug('terminating session');

        reason_phrase = options.reason_phrase || JsSIP_C.REASON_PHRASE[status_code] || '';

        if (status_code && (status_code < 200 || status_code >= 700))
        {
          throw new TypeError(`Invalid status_code: ${status_code}`);
        }
        else if (status_code)
        {
          extraHeaders.push(`Reason: SIP ;cause=${status_code}; text="${reason_phrase}"`);
        }

        this.sendRequest(JsSIP_C.BYE, {
          extraHeaders,
          body
        });

        this._ended('local', null, cause);
    }
  }

  sendDTMF(tones, options = {})
  {
    debug('sendDTMF() | tones: %s', tones);

    let position = 0;
    let duration = options.duration || null;
    let interToneGap = options.interToneGap || null;

    if (tones === undefined)
    {
      throw new TypeError('Not enough arguments');
    }

    // Check Session Status.
    if (this._status !== C.STATUS_CONFIRMED && this._status !== C.STATUS_WAITING_FOR_ACK)
    {
      throw new Exceptions.InvalidStateError(this._status);
    }

    // Convert to string.
    if (typeof tones === 'number')
    {
      tones = tones.toString();
    }

    // Check tones.
    if (!tones || typeof tones !== 'string' || !tones.match(/^[0-9A-DR#*,]+$/i))
    {
      throw new TypeError(`Invalid tones: ${tones}`);
    }

    // Check duration.
    if (duration && !Utils.isDecimal(duration))
    {
      throw new TypeError(`Invalid tone duration: ${duration}`);
    }
    else if (!duration)
    {
      duration = RTCSession_DTMF.C.DEFAULT_DURATION;
    }
    else if (duration < RTCSession_DTMF.C.MIN_DURATION)
    {
      debug(`"duration" value is lower than the minimum allowed, setting it to ${RTCSession_DTMF.C.MIN_DURATION} milliseconds`);
      duration = RTCSession_DTMF.C.MIN_DURATION;
    }
    else if (duration > RTCSession_DTMF.C.MAX_DURATION)
    {
      debug(`"duration" value is greater than the maximum allowed, setting it to ${RTCSession_DTMF.C.MAX_DURATION} milliseconds`);
      duration = RTCSession_DTMF.C.MAX_DURATION;
    }
    else
    {
      duration = Math.abs(duration);
    }
    options.duration = duration;

    // Check interToneGap.
    if (interToneGap && !Utils.isDecimal(interToneGap))
    {
      throw new TypeError(`Invalid interToneGap: ${interToneGap}`);
    }
    else if (!interToneGap)
    {
      interToneGap = RTCSession_DTMF.C.DEFAULT_INTER_TONE_GAP;
    }
    else if (interToneGap < RTCSession_DTMF.C.MIN_INTER_TONE_GAP)
    {
      debug(`"interToneGap" value is lower than the minimum allowed, setting it to ${RTCSession_DTMF.C.MIN_INTER_TONE_GAP} milliseconds`);
      interToneGap = RTCSession_DTMF.C.MIN_INTER_TONE_GAP;
    }
    else
    {
      interToneGap = Math.abs(interToneGap);
    }

    if (this._tones)
    {
      // Tones are already queued, just add to the queue.
      this._tones += tones;

      return;
    }

    this._tones = tones;

    // Send the first tone.
    _sendDTMF.call(this);

    function _sendDTMF()
    {
      let timeout;

      if (this._status === C.STATUS_TERMINATED ||
          !this._tones || position >= this._tones.length)
      {
        // Stop sending DTMF.
        this._tones = null;

        return;
      }

      const tone = this._tones[position];

      position += 1;

      if (tone === ',')
      {
        timeout = 2000;
      }
      else
      {
        const dtmf = new RTCSession_DTMF(this);

        options.eventHandlers = {
          onFailed : () => { this._tones = null; }
        };
        dtmf.send(tone, options);
        timeout = duration + interToneGap;
      }

      // Set timeout for the next tone.
      setTimeout(_sendDTMF.bind(this), timeout);
    }
  }

  sendInfo(contentType, body, options = {})
  {
    debug('sendInfo()');

    // Check Session Status.
    if (this._status !== C.STATUS_CONFIRMED && this._status !== C.STATUS_WAITING_FOR_ACK)
    {
      throw new Exceptions.InvalidStateError(this._status);
    }

    const info = new RTCSession_Info(this);

    info.send(contentType, body, options);
  }

  renegotiate(options = {}, done)
  {
    debug('renegotiate()');

    const rtcOfferConstraints = options.rtcOfferConstraints || null;

    if (this._status !== C.STATUS_WAITING_FOR_ACK && this._status !== C.STATUS_CONFIRMED)
    {
      return false;
    }

    if (! this._isReadyToReOffer())
    {
      return false;
    }

    const eventHandlers = {
      succeeded : () =>
      {
        if (done) { done(); }
      },
      failed : () =>
      {
        this.terminate({
          cause         : JsSIP_C.causes.WEBRTC_ERROR,
          status_code   : 500,
          reason_phrase : 'Media Renegotiation Failed'
        });
      }
    };

    if (options.useUpdate)
    {
      this._sendUpdate({
        sdpOffer     : true,
        eventHandlers,
        rtcOfferConstraints,
        extraHeaders : options.extraHeaders
      });
    }
    else
    {
      this._sendReinvite({
        eventHandlers,
        rtcOfferConstraints,
        extraHeaders : options.extraHeaders
      });
    }

    return true;
  }

  /**
   * Send a generic in-dialog Request
   */
  sendRequest(method, options)
  {
    debug('sendRequest()');

    return this._dialog.sendRequest(method, options);
  }

  /**
   * In dialog Request Reception
   */
  receiveRequest(request)
  {
    debug('receiveRequest()');

    if (request.method === JsSIP_C.CANCEL)
    {
      /* RFC3261 15 States that a UAS may have accepted an invitation while a CANCEL
      * was in progress and that the UAC MAY continue with the session established by
      * any 2xx response, or MAY terminate with BYE. JsSIP does continue with the
      * established session. So the CANCEL is processed only if the session is not yet
      * established.
      */

      /*
      * Terminate the whole session in case the user didn't accept (or yet send the answer)
      * nor reject the request opening the session.
      */
      if (this._status === C.STATUS_WAITING_FOR_ANSWER ||
          this._status === C.STATUS_ANSWERED)
      {
        this._status = C.STATUS_CANCELED;
        this._request.reply(487);
        this._failed('remote', request, JsSIP_C.causes.CANCELED);
      }
    }
    else
    {
      // Requests arriving here are in-dialog requests.
      switch (request.method)
      {
        case JsSIP_C.ACK:
          debug('emit "ackReceived"');
          this.emit('ackReceived', { request });

          if (this._status !== C.STATUS_WAITING_FOR_ACK)
          {
            return;
          }

          // Update signaling status.
          this._status = C.STATUS_CONFIRMED;

          clearTimeout(this._timers.ackTimer);
          clearTimeout(this._timers.invite2xxTimer);

          if (this._late_sdp)
          {
            if (!request.body)
            {
              this.terminate({
                cause       : JsSIP_C.causes.MISSING_SDP,
                status_code : 400
              });
              break;
            }

            const e = { originator: 'remote', type: 'answer', sdp: request.body };

            debug('emit "sdp"');
            this.emit('sdp', e);

            const answer = new RTCSessionDescription({ type: 'answer', sdp: e.sdp });

            this._connectionPromiseQueue = this._connectionPromiseQueue
              .then(() => this._connection.setRemoteDescription(answer))
              .then(() =>
              {
                if (!this._is_confirmed)
                {
                  this._confirmed('remote', request);
                }
              })
              .catch((error) =>
              {
                this.terminate({
                  cause       : JsSIP_C.causes.BAD_MEDIA_DESCRIPTION,
                  status_code : 488
                });

                debugerror('emit "peerconnection:setremotedescriptionfailed" [error:%o]', error);
                this.emit('peerconnection:setremotedescriptionfailed', error);
              });
          }
          else
          if (!this._is_confirmed)
          {
            this._confirmed('remote', request);
          }

          break;
        case JsSIP_C.BYE:
          if (this._status === C.STATUS_CONFIRMED ||
              this._status === C.STATUS_WAITING_FOR_ACK)
          {
            const e = { originator: 'remote', responseExtraHeaders: [] };

            debug('emit "byeReceived"');
            this.emit('byeReceived', e);

            request.reply(200, null, e.responseExtraHeaders);
            this._ended('remote', request, JsSIP_C.causes.BYE);
          }
          else
          {
            request.reply(403, 'Wrong Status');
          }
          break;
        case JsSIP_C.INVITE:
          if (this._status === C.STATUS_CONFIRMED)
          {
            this._receiveReinvite(request);
          }
          else
          {
            request.reply(403, 'Wrong Status');
          }
          break;
        case JsSIP_C.INFO:
          if (this._status === C.STATUS_1XX_RECEIVED ||
              this._status === C.STATUS_WAITING_FOR_ANSWER ||
              this._status === C.STATUS_ANSWERED ||
              this._status === C.STATUS_WAITING_FOR_ACK ||
              this._status === C.STATUS_CONFIRMED)
          {
            const contentType = request.getHeader('content-type');

            if (contentType && (contentType.match(/^application\/dtmf-relay/i)))
            {
              new RTCSession_DTMF(this).init_incoming(request);
            }
            else if (contentType !== undefined)
            {
              new RTCSession_Info(this).init_incoming(request);
            }
            else
            {
              request.reply(415);
            }
          }
          else
          {
            request.reply(403, 'Wrong Status');
          }
          break;
        case JsSIP_C.UPDATE:
          if (this._status === C.STATUS_CONFIRMED)
          {
            this._receiveUpdate(request);
          }
          else
          {
            request.reply(403, 'Wrong Status');
          }
          break;
        default:
          request.reply(501);
      }
    }
  }

  /**
   * Session Callbacks
   */

  onTransportError()
  {
    debugerror('onTransportError()');

    if (this._status !== C.STATUS_TERMINATED)
    {
      this.terminate({
        status_code   : 500,
        reason_phrase : JsSIP_C.causes.CONNECTION_ERROR,
        cause         : JsSIP_C.causes.CONNECTION_ERROR
      });
    }
  }

  onRequestTimeout()
  {
    debugerror('onRequestTimeout()');

    if (this._status !== C.STATUS_TERMINATED)
    {
      this.terminate({
        status_code   : 408,
        reason_phrase : JsSIP_C.causes.REQUEST_TIMEOUT,
        cause         : JsSIP_C.causes.REQUEST_TIMEOUT
      });
    }
  }

  onDialogError()
  {
    debugerror('onDialogError()');

    if (this._status !== C.STATUS_TERMINATED)
    {
      this.terminate({
        status_code   : 500,
        reason_phrase : JsSIP_C.causes.DIALOG_ERROR,
        cause         : JsSIP_C.causes.DIALOG_ERROR
      });
    }
  }

  // Called from DTMF handler.
  newDTMF(data)
  {
    debug('newDTMF()');

    this.emit('newDTMF', data);
  }

  // Called from Info handler.
  newInfo(data)
  {
    debug('newInfo()');

    this.emit('newInfo', data);
  }

  /**
   * Check if RTCSession is ready for an outgoing re-INVITE or UPDATE with SDP.
   */
  _isReadyToReOffer()
  {
    if (! this._rtcReady)
    {
      debug('_isReadyToReOffer() | internal WebRTC status not ready');

      return false;
    }

    // No established yet.
    if (! this._dialog)
    {
      debug('_isReadyToReOffer() | session not established yet');

      return false;
    }

    // Another INVITE transaction is in progress.
    if (this._dialog.uac_pending_reply === true ||
        this._dialog.uas_pending_reply === true)
    {
      debug('_isReadyToReOffer() | there is another INVITE/UPDATE transaction in progress');

      return false;
    }

    return true;
  }

  _close()
  {
    debug('close()');

    if (this._status === C.STATUS_TERMINATED)
    {
      return;
    }

    this._status = C.STATUS_TERMINATED;

    // Terminate signaling.

    // Clear SIP timers.
    for (const timer in this._timers)
    {
      if (Object.prototype.hasOwnProperty.call(this._timers, timer))
      {
        clearTimeout(this._timers[timer]);
      }
    }

    // Clear Session Timers.
    clearTimeout(this._sessionTimers.timer);

    // Terminate confirmed dialog.
    if (this._dialog)
    {
      this._dialog.terminate();
      delete this._dialog;
    }

    // Terminate early dialogs.
    for (const dialog in this._earlyDialogs)
    {
      if (Object.prototype.hasOwnProperty.call(this._earlyDialogs, dialog))
      {
        this._earlyDialogs[dialog].terminate();
        delete this._earlyDialogs[dialog];
      }
    }

    this._ua.destroyRTCSession(this);
  }

  /**
   * Private API.
   */

  /**
   * RFC3261 13.3.1.4
   * Response retransmissions cannot be accomplished by transaction layer
   *  since it is destroyed when receiving the first 2xx answer
   */
  _setInvite2xxTimer(request, body)
  {
    let timeout = Timers.T1;

    function invite2xxRetransmission()
    {
      if (this._status !== C.STATUS_WAITING_FOR_ACK)
      {
        return;
      }

      request.reply(200, null, [ `Contact: ${this._contact}` ], body);

      if (timeout < Timers.T2)
      {
        timeout = timeout * 2;
        if (timeout > Timers.T2)
        {
          timeout = Timers.T2;
        }
      }

      this._timers.invite2xxTimer = setTimeout(
        invite2xxRetransmission.bind(this), timeout);
    }

    this._timers.invite2xxTimer = setTimeout(
      invite2xxRetransmission.bind(this), timeout);
  }


  /**
   * RFC3261 14.2
   * If a UAS generates a 2xx response and never receives an ACK,
   *  it SHOULD generate a BYE to terminate the dialog.
   */
  _setACKTimer()
  {
    this._timers.ackTimer = setTimeout(() =>
    {
      if (this._status === C.STATUS_WAITING_FOR_ACK)
      {
        debug('no ACK received, terminating the session');

        clearTimeout(this._timers.invite2xxTimer);
        this.sendRequest(JsSIP_C.BYE);
        this._ended('remote', null, JsSIP_C.causes.NO_ACK);
      }
    }, Timers.TIMER_H);
  }

  _createLocalDescription(type, constraints)
  {
    debug('createLocalDescription()');

    if (type !== 'offer' && type !== 'answer')
      throw new Error(`createLocalDescription() | invalid type "${type}"`);

    const connection = this._connection;

    this._rtcReady = false;

    return Promise.resolve()
      // Create Offer or Answer.
      .then(() =>
      {
        if (type === 'offer')
        {
          return connection.createOffer(constraints)
            .catch((error) =>
            {
              debugerror('emit "peerconnection:createofferfailed" [error:%o]', error);

              this.emit('peerconnection:createofferfailed', error);

              return Promise.reject(error);
            });
        }
        else
        {
          return connection.createAnswer(constraints)
            .catch((error) =>
            {
              debugerror('emit "peerconnection:createanswerfailed" [error:%o]', error);

              this.emit('peerconnection:createanswerfailed', error);

              return Promise.reject(error);
            });
        }
      })
      // Set local description.
      .then((desc) =>
      {
        return connection.setLocalDescription(desc)
          .catch((error) =>
          {
            this._rtcReady = true;

            debugerror('emit "peerconnection:setlocaldescriptionfailed" [error:%o]', error);

            this.emit('peerconnection:setlocaldescriptionfailed', error);

            return Promise.reject(error);
          });
      })
      .then(() =>
      {
        // Resolve right away if 'pc.iceGatheringState' is 'complete'.
        if (connection.iceGatheringState === 'complete')
        {
          this._rtcReady = true;

          const e = { originator: 'local', type: type, sdp: connection.localDescription.sdp };

          debug('emit "sdp"');

          this.emit('sdp', e);

          return Promise.resolve(e.sdp);
        }

        // Add 'pc.onicencandidate' event handler to resolve on last candidate.
        return new Promise((resolve) =>
        {
          let finished = false;
          let iceCandidateListener;
          let iceGatheringStateListener;

          const ready = () =>
          {
            connection.removeEventListener('icecandidate', iceCandidateListener);
            connection.removeEventListener('icegatheringstatechange', iceGatheringStateListener);

            finished = true;
            this._rtcReady = true;

            const e = { originator: 'local', type: type, sdp: connection.localDescription.sdp };

            debug('emit "sdp"');

            this.emit('sdp', e);

            resolve(e.sdp);
          };

          connection.addEventListener('icecandidate', iceCandidateListener = (event) =>
          {
            const candidate = event.candidate;

            if (candidate)
            {
              this.emit('icecandidate', {
                candidate,
                ready
              });
            }

            else if (! finished)
            {
              ready();
            }
          });

          connection.addEventListener('icegatheringstatechange', iceGatheringStateListener = () =>
          {
            if ((connection.iceGatheringState === 'complete') && !finished)
            {
              ready();
            }
          });
        });
      });
  }

  /**
   * Dialog Management
   */
  _createDialog(message, type, early)
  {
    const local_tag = (type === 'UAS') ? message.to_tag : message.from_tag;
    const remote_tag = (type === 'UAS') ? message.from_tag : message.to_tag;
    const id = message.call_id + local_tag + remote_tag;

    let early_dialog = this._earlyDialogs[id];

    // Early Dialog.
    if (early)
    {
      if (early_dialog)
      {
        return true;
      }
      else
      {
        early_dialog = new Dialog(this, message, type, Dialog.C.STATUS_EARLY);

        // Dialog has been successfully created.
        if (early_dialog.error)
        {
          debug(early_dialog.error);
          this._failed('remote', message, JsSIP_C.causes.INTERNAL_ERROR);

          return false;
        }
        else
        {
          this._earlyDialogs[id] = early_dialog;

          return true;
        }
      }
    }

    // Confirmed Dialog.
    else
    {
      this._from_tag = message.from_tag;
      this._to_tag = message.to_tag;

      // In case the dialog is in _early_ state, update it.
      if (early_dialog)
      {
        early_dialog.update(message, type);
        this._dialog = early_dialog;
        delete this._earlyDialogs[id];

        return true;
      }

      // Otherwise, create a _confirmed_ dialog.
      const dialog = new Dialog(this, message, type);

      if (dialog.error)
      {
        debug(dialog.error);
        this._failed('remote', message, JsSIP_C.causes.INTERNAL_ERROR);

        return false;
      }
      else
      {
        this._dialog = dialog;

        return true;
      }
    }
  }

  /**
   * In dialog INVITE Reception
   */

  _receiveReinvite(request)
  {
    debug('receiveReinvite()');

    const contentType = request.getHeader('Content-Type');
    const data = {
      request,
      callback : undefined,
      reject   : reject.bind(this)
    };

    let rejected = false;

    function reject(options = {})
    {
      rejected = true;

      const status_code = options.status_code || 403;
      const reason_phrase = options.reason_phrase || '';
      const extraHeaders = Utils.cloneArray(options.extraHeaders);

      if (this._status !== C.STATUS_CONFIRMED)
      {
        return false;
      }

      if (status_code < 300 || status_code >= 700)
      {
        throw new TypeError(`Invalid status_code: ${status_code}`);
      }

      request.reply(status_code, reason_phrase, extraHeaders);
    }

    // Emit 'reinvite'.
    this.emit('reinvite', data);

    if (rejected)
    {
      return;
    }

    this._late_sdp = false;

    // Request without SDP.
    if (!request.body)
    {
      this._late_sdp = true;
      this._connectionPromiseQueue = this._connectionPromiseQueue
        .then(() => this._createLocalDescription('offer', this._rtcOfferConstraints))
        .then((sdp) =>
        {
          sendAnswer.call(this, sdp);
        })
        .catch(() =>
        {
          request.reply(500);
        });

      return;
    }

    // Request with SDP.
    if (contentType !== 'application/sdp')
    {
      debug('invalid Content-Type');
      request.reply(415);

      return;
    }

    this._processInDialogSdpOffer(request)
      // Send answer.
      .then((desc) =>
      {
        if (this._status === C.STATUS_TERMINATED)
        {
          return;
        }

        sendAnswer.call(this, desc);
      })
      .catch((error) =>
      {
        debugerror(error);
      });

    function sendAnswer(desc)
    {
      const extraHeaders = [ `Contact: ${this._contact}` ];

      this._handleSessionTimersInIncomingRequest(request, extraHeaders);

      request.reply(200, null, extraHeaders, desc,
        () =>
        {
          this._status = C.STATUS_WAITING_FOR_ACK;
          this._setInvite2xxTimer(request, desc);
          this._setACKTimer();
        }
      );

      // If callback is given execute it.
      if (typeof data.callback === 'function')
      {
        data.callback();
      }
    }
  }

  /**
   * In dialog UPDATE Reception
   */
  _receiveUpdate(request)
  {
    debug('receiveUpdate()');

    const contentType = request.getHeader('Content-Type');
    const data = {
      request,
      callback : undefined,
      reject   : reject.bind(this)
    };

    let rejected = false;

    function reject(options = {})
    {
      rejected = true;

      const status_code = options.status_code || 403;
      const reason_phrase = options.reason_phrase || '';
      const extraHeaders = Utils.cloneArray(options.extraHeaders);

      if (this._status !== C.STATUS_CONFIRMED)
      {
        return false;
      }

      if (status_code < 300 || status_code >= 700)
      {
        throw new TypeError(`Invalid status_code: ${status_code}`);
      }

      request.reply(status_code, reason_phrase, extraHeaders);
    }

    // Emit 'update'.
    this.emit('update', data);

    if (rejected)
    {
      return;
    }

    if (! request.body)
    {
      sendAnswer.call(this, null);

      return;
    }

    if (contentType !== 'application/sdp')
    {
      debug('invalid Content-Type');

      request.reply(415);

      return;
    }

    this._processInDialogSdpOffer(request)
      // Send answer.
      .then((desc) =>
      {
        if (this._status === C.STATUS_TERMINATED)
        {
          return;
        }

        sendAnswer.call(this, desc);
      })
      .catch((error) =>
      {
        debugerror(error);
      });

    function sendAnswer(desc)
    {
      const extraHeaders = [ `Contact: ${this._contact}` ];

      this._handleSessionTimersInIncomingRequest(request, extraHeaders);

      request.reply(200, null, extraHeaders, desc);

      // If callback is given execute it.
      if (typeof data.callback === 'function')
      {
        data.callback();
      }
    }
  }

  _processInDialogSdpOffer(request)
  {
    debug('_processInDialogSdpOffer()');

    const e = { originator: 'remote', type: 'offer', sdp: request.body };

    debug('emit "sdp"');
    this.emit('sdp', e);

    const offer = new RTCSessionDescription({ type: 'offer', sdp: e.sdp });

    this._connectionPromiseQueue = this._connectionPromiseQueue
      // Set remote description.
      .then(() =>
      {
        if (this._status === C.STATUS_TERMINATED)
        {
          throw new Error('terminated');
        }

        return this._connection.setRemoteDescription(offer)
          .catch((error) =>
          {
            request.reply(488);
            debugerror('emit "peerconnection:setremotedescriptionfailed" [error:%o]', error);

            this.emit('peerconnection:setremotedescriptionfailed', error);

            throw new Error('peerconnection.setRemoteDescription() failed');
          });
      })
      // Create local description.
      .then(() =>
      {
        if (this._status === C.STATUS_TERMINATED)
        {
          throw new Error('terminated');
        }

        return this._createLocalDescription('answer', this._rtcAnswerConstraints)
          .catch(() =>
          {
            request.reply(500);

            throw new Error('_createLocalDescription() failed');
          });
      });

    return this._connectionPromiseQueue;
  }

  /**
   * Initial Request Sender
   */
  _sendInitialRequest(sdp)
  {
    const request_sender = new RequestSender(this._ua, this._request, {
      onRequestTimeout : () =>
      {
        this.onRequestTimeout();
      },
      onTransportError : () =>
      {
        this.onTransportError();
      },
      // Update the request on authentication.
      onAuthenticated : (request) =>
      {
        this._request = request;
      },
      onReceiveResponse : (response) =>
      {
        this._receiveInviteResponse(response);
      }
    });

    // This Promise is resolved within the next iteration, so the app has now
    // a chance to set events such as 'peerconnection' and 'connecting'.
    Promise.resolve()
      .then(() =>
      {
        if (this._status === C.STATUS_TERMINATED)
        {
          throw new Error('terminated');
        }

        // TODO: should this be triggered here?
        this._connecting(this._request);
      })
      .then(() =>
      {
        if (this._is_canceled || this._status === C.STATUS_TERMINATED)
        {
          throw new Error('terminated');
        }

        this._request.body = sdp;
        this._status = C.STATUS_INVITE_SENT;

        debug('emit "sending" [request:%o]', this._request);

        // Emit 'sending' so the app can mangle the body before the request is sent.
        this.emit('sending', {
          request : this._request
        });

        request_sender.send();
      })
      .catch((error) =>
      {
        if (this._status === C.STATUS_TERMINATED)
        {
          return;
        }

        debugerror(error);
      });
  }

  /**
   * Reception of Response for Initial INVITE
   */
  _receiveInviteResponse(response)
  {
    debug('receiveInviteResponse()');

    // Handle 2XX retransmissions and responses from forked requests.
    if (this._dialog && (response.status_code >=200 && response.status_code <=299))
    {

      /*
       * If it is a retransmission from the endpoint that established
       * the dialog, send an ACK
       */
      if (this._dialog.id.call_id === response.call_id &&
          this._dialog.id.local_tag === response.from_tag &&
          this._dialog.id.remote_tag === response.to_tag)
      {
        this.sendRequest(JsSIP_C.ACK);

        return;
      }

      // If not, send an ACK  and terminate.
      else
      {
        const dialog = new Dialog(this, response, 'UAC');

        if (dialog.error !== undefined)
        {
          debug(dialog.error);

          return;
        }

        this.sendRequest(JsSIP_C.ACK);
        this.sendRequest(JsSIP_C.BYE);

        return;
      }

    }

    // Proceed to cancellation if the user requested.
    if (this._is_canceled)
    {
      if (response.status_code >= 100 && response.status_code < 200)
      {
        this._request.cancel(this._cancel_reason);
      }
      else if (response.status_code >= 200 && response.status_code < 299)
      {
        this._acceptAndTerminate(response);
      }

      return;
    }

    if (this._status !== C.STATUS_INVITE_SENT && this._status !== C.STATUS_1XX_RECEIVED)
    {
      return;
    }

    switch (true)
    {
      case /^100$/.test(response.status_code):
        this._status = C.STATUS_1XX_RECEIVED;
        break;

      case /^1[0-9]{2}$/.test(response.status_code):
      {
        // Do nothing with 1xx responses without To tag.
        if (!response.to_tag)
        {
          debug('1xx response received without to tag');
          break;
        }

        // Create Early Dialog if 1XX comes with contact.
        if (response.hasHeader('contact'))
        {
          // An error on dialog creation will fire 'failed' event.
          if (! this._createDialog(response, 'UAC', true))
          {
            break;
          }
        }

        this._status = C.STATUS_1XX_RECEIVED;
        this._progress('remote', response);

        if (!response.body)
        {
          break;
        }

        const e = { originator: 'remote', type: 'answer', sdp: response.body };

        debug('emit "sdp"');
        this.emit('sdp', e);

        const answer = new RTCSessionDescription({ type: 'answer', sdp: e.sdp });

        this._connectionPromiseQueue = this._connectionPromiseQueue
          .then(() => this._connection.setRemoteDescription(answer))
          .catch((error) =>
          {
            debugerror('emit "peerconnection:setremotedescriptionfailed" [error:%o]', error);

            this.emit('peerconnection:setremotedescriptionfailed', error);
          });
        break;
      }

      case /^2[0-9]{2}$/.test(response.status_code):
      {
        this._status = C.STATUS_CONFIRMED;

        if (!response.body)
        {
          this._acceptAndTerminate(response, 400, JsSIP_C.causes.MISSING_SDP);
          this._failed('remote', response, JsSIP_C.causes.BAD_MEDIA_DESCRIPTION);
          break;
        }

        // An error on dialog creation will fire 'failed' event.
        if (! this._createDialog(response, 'UAC'))
        {
          break;
        }

        const e = { originator: 'remote', type: 'answer', sdp: response.body };

        debug('emit "sdp"');
        this.emit('sdp', e);

        const answer = new RTCSessionDescription({ type: 'answer', sdp: e.sdp });

        this._connectionPromiseQueue = this._connectionPromiseQueue
          .then(() =>
          {
            // Be ready for 200 with SDP after a 180/183 with SDP.
            // We created a SDP 'answer' for it, so check the current signaling state.
            if (this._connection.signalingState === 'stable')
            {
              return this._connection.createOffer(this._rtcOfferConstraints)
                .then((offer) => this._connection.setLocalDescription(offer))
                .catch((error) =>
                {
                  this._acceptAndTerminate(response, 500, error.toString());
                  this._failed('local', response, JsSIP_C.causes.WEBRTC_ERROR);
                });
            }
          })
          .then(() =>
          {
            this._connection.setRemoteDescription(answer)
              .then(() =>
              {
                // Handle Session Timers.
                this._handleSessionTimersInIncomingResponse(response);

                this._accepted('remote', response);
                this.sendRequest(JsSIP_C.ACK);
                this._confirmed('local', null);
              })
              .catch((error) =>
              {
                this._acceptAndTerminate(response, 488, 'Not Acceptable Here');
                this._failed('remote', response, JsSIP_C.causes.BAD_MEDIA_DESCRIPTION);

                debugerror('emit "peerconnection:setremotedescriptionfailed" [error:%o]', error);

                this.emit('peerconnection:setremotedescriptionfailed', error);
              });
          });
        break;
      }

      default:
      {
        const cause = Utils.sipErrorCause(response.status_code);

        this._failed('remote', response, cause);
      }
    }
  }

  /**
   * Send Re-INVITE
   */
  _sendReinvite(options = {})
  {
    debug('sendReinvite()');

    const extraHeaders = Utils.cloneArray(options.extraHeaders);
    const eventHandlers = options.eventHandlers || {};
    const rtcOfferConstraints = options.rtcOfferConstraints ||
      this._rtcOfferConstraints || null;

    let succeeded = false;

    extraHeaders.push(`Contact: ${this._contact}`);
    extraHeaders.push('Content-Type: application/sdp');

    // Session Timers.
    if (this._sessionTimers.running)
    {
      extraHeaders.push(`Session-Expires: ${this._sessionTimers.currentExpires};refresher=${this._sessionTimers.refresher ? 'uac' : 'uas'}`);
    }

    this._connectionPromiseQueue = this._connectionPromiseQueue
      .then(() => this._createLocalDescription('offer', rtcOfferConstraints))
      .then((sdp) =>
      {
        const e = { originator: 'local', type: 'offer', sdp };

        debug('emit "sdp"');
        this.emit('sdp', e);

        this.sendRequest(JsSIP_C.INVITE, {
          extraHeaders,
          body          : sdp,
          eventHandlers : {
            onSuccessResponse : (response) =>
            {
              onSucceeded.call(this, response);
              succeeded = true;
            },
            onErrorResponse : (response) =>
            {
              onFailed.call(this, response);
            },
            onTransportError : () =>
            {
              this.onTransportError(); // Do nothing because session ends.
            },
            onRequestTimeout : () =>
            {
              this.onRequestTimeout(); // Do nothing because session ends.
            },
            onDialogError : () =>
            {
              this.onDialogError(); // Do nothing because session ends.
            }
          }
        });
      })
      .catch(() =>
      {
        onFailed();
      });

    function onSucceeded(response)
    {
      if (this._status === C.STATUS_TERMINATED)
      {
        return;
      }

      this.sendRequest(JsSIP_C.ACK);

      // If it is a 2XX retransmission exit now.
      if (succeeded) { return; }

      // Handle Session Timers.
      this._handleSessionTimersInIncomingResponse(response);

      // Must have SDP answer.
      if (! response.body)
      {
        onFailed.call(this);

        return;
      }
      else if (response.getHeader('Content-Type') !== 'application/sdp')
      {
        onFailed.call(this);

        return;
      }

      const e = { originator: 'remote', type: 'answer', sdp: response.body };

      debug('emit "sdp"');
      this.emit('sdp', e);

      const answer = new RTCSessionDescription({ type: 'answer', sdp: e.sdp });

      this._connectionPromiseQueue = this._connectionPromiseQueue
        .then(() => this._connection.setRemoteDescription(answer))
        .then(() =>
        {
          if (eventHandlers.succeeded)
          {
            eventHandlers.succeeded(response);
          }
        })
        .catch((error) =>
        {
          onFailed.call(this);

          debugerror('emit "peerconnection:setremotedescriptionfailed" [error:%o]', error);

          this.emit('peerconnection:setremotedescriptionfailed', error);
        });
    }

    function onFailed(response)
    {
      if (eventHandlers.failed)
      {
        eventHandlers.failed(response);
      }
    }
  }

  /**
   * Send UPDATE
   */
  _sendUpdate(options = {})
  {
    debug('sendUpdate()');

    const extraHeaders = Utils.cloneArray(options.extraHeaders);
    const eventHandlers = options.eventHandlers || {};
    const rtcOfferConstraints = options.rtcOfferConstraints ||
      this._rtcOfferConstraints || null;
    const sdpOffer = options.sdpOffer || false;

    let succeeded = false;

    extraHeaders.push(`Contact: ${this._contact}`);

    // Session Timers.
    if (this._sessionTimers.running)
    {
      extraHeaders.push(`Session-Expires: ${this._sessionTimers.currentExpires};refresher=${this._sessionTimers.refresher ? 'uac' : 'uas'}`);
    }

    if (sdpOffer)
    {
      extraHeaders.push('Content-Type: application/sdp');

      this._connectionPromiseQueue = this._connectionPromiseQueue
        .then(() => this._createLocalDescription('offer', rtcOfferConstraints))
        .then((sdp) =>
        {
          const e = { originator: 'local', type: 'offer', sdp };

          debug('emit "sdp"');
          this.emit('sdp', e);

          this.sendRequest(JsSIP_C.UPDATE, {
            extraHeaders,
            body          : sdp,
            eventHandlers : {
              onSuccessResponse : (response) =>
              {
                onSucceeded.call(this, response);
                succeeded = true;
              },
              onErrorResponse : (response) =>
              {
                onFailed.call(this, response);
              },
              onTransportError : () =>
              {
                this.onTransportError(); // Do nothing because session ends.
              },
              onRequestTimeout : () =>
              {
                this.onRequestTimeout(); // Do nothing because session ends.
              },
              onDialogError : () =>
              {
                this.onDialogError(); // Do nothing because session ends.
              }
            }
          });
        })
        .catch(() =>
        {
          onFailed.call(this);
        });
    }

    // No SDP.
    else
    {
      this.sendRequest(JsSIP_C.UPDATE, {
        extraHeaders,
        eventHandlers : {
          onSuccessResponse : (response) =>
          {
            onSucceeded.call(this, response);
          },
          onErrorResponse : (response) =>
          {
            onFailed.call(this, response);
          },
          onTransportError : () =>
          {
            this.onTransportError(); // Do nothing because session ends.
          },
          onRequestTimeout : () =>
          {
            this.onRequestTimeout(); // Do nothing because session ends.
          },
          onDialogError : () =>
          {
            this.onDialogError(); // Do nothing because session ends.
          }
        }
      });
    }

    function onSucceeded(response)
    {
      if (this._status === C.STATUS_TERMINATED)
      {
        return;
      }

      // If it is a 2XX retransmission exit now.
      if (succeeded) { return; }

      // Handle Session Timers.
      this._handleSessionTimersInIncomingResponse(response);

      // Must have SDP answer.
      if (sdpOffer)
      {
        if (! response.body)
        {
          onFailed.call(this);

          return;
        }
        else if (response.getHeader('Content-Type') !== 'application/sdp')
        {
          onFailed.call(this);

          return;
        }

        const e = { originator: 'remote', type: 'answer', sdp: response.body };

        debug('emit "sdp"');
        this.emit('sdp', e);

        const answer = new RTCSessionDescription({ type: 'answer', sdp: e.sdp });

        this._connectionPromiseQueue = this._connectionPromiseQueue
          .then(() => this._connection.setRemoteDescription(answer))
          .then(() =>
          {
            if (eventHandlers.succeeded)
            {
              eventHandlers.succeeded(response);
            }
          })
          .catch((error) =>
          {
            onFailed.call(this);

            debugerror('emit "peerconnection:setremotedescriptionfailed" [error:%o]', error);

            this.emit('peerconnection:setremotedescriptionfailed', error);
          });
      }
      // No SDP answer.
      else
      if (eventHandlers.succeeded)
      {
        eventHandlers.succeeded(response);
      }
    }

    function onFailed(response)
    {
      if (eventHandlers.failed) { eventHandlers.failed(response); }
    }
  }

  _acceptAndTerminate(response, status_code, reason_phrase)
  {
    debug('acceptAndTerminate()');

    const extraHeaders = [];

    if (status_code)
    {
      reason_phrase = reason_phrase || JsSIP_C.REASON_PHRASE[status_code] || '';
      extraHeaders.push(`Reason: SIP ;cause=${status_code}; text="${reason_phrase}"`);
    }

    // An error on dialog creation will fire 'failed' event.
    if (this._dialog || this._createDialog(response, 'UAC'))
    {
      this.sendRequest(JsSIP_C.ACK);
      this.sendRequest(JsSIP_C.BYE, {
        extraHeaders
      });
    }

    // Update session status.
    this._status = C.STATUS_TERMINATED;
  }

  /**
   * Handle SessionTimers for an incoming INVITE or UPDATE.
   * @param  {IncomingRequest} request
   * @param  {Array} responseExtraHeaders  Extra headers for the 200 response.
   */
  _handleSessionTimersInIncomingRequest(request, responseExtraHeaders)
  {
    if (! this._sessionTimers.enabled) { return; }

    let session_expires_refresher;

    if (request.session_expires && request.session_expires >= JsSIP_C.MIN_SESSION_EXPIRES)
    {
      this._sessionTimers.currentExpires = request.session_expires;
      session_expires_refresher = request.session_expires_refresher || 'uas';
    }
    else
    {
      this._sessionTimers.currentExpires = this._sessionTimers.defaultExpires;
      session_expires_refresher = 'uas';
    }

    responseExtraHeaders.push(`Session-Expires: ${this._sessionTimers.currentExpires};refresher=${session_expires_refresher}`);

    this._sessionTimers.refresher = (session_expires_refresher === 'uas');
    this._runSessionTimer();
  }

  /**
   * Handle SessionTimers for an incoming response to INVITE or UPDATE.
   * @param  {IncomingResponse} response
   */
  _handleSessionTimersInIncomingResponse(response)
  {
    if (! this._sessionTimers.enabled) { return; }

    let session_expires_refresher;

    if (response.session_expires &&
        response.session_expires >= JsSIP_C.MIN_SESSION_EXPIRES)
    {
      this._sessionTimers.currentExpires = response.session_expires;
      session_expires_refresher = response.session_expires_refresher || 'uac';
    }
    else
    {
      this._sessionTimers.currentExpires = this._sessionTimers.defaultExpires;
      session_expires_refresher = 'uac';
    }

    this._sessionTimers.refresher = (session_expires_refresher === 'uac');
    this._runSessionTimer();
  }

  _runSessionTimer()
  {
    const expires = this._sessionTimers.currentExpires;

    this._sessionTimers.running = true;

    clearTimeout(this._sessionTimers.timer);

    // I'm the refresher.
    if (this._sessionTimers.refresher)
    {
      this._sessionTimers.timer = setTimeout(() =>
      {
        if (this._status === C.STATUS_TERMINATED) { return; }

        debug('runSessionTimer() | sending session refresh request');

        if (this._sessionTimers.refreshMethod === JsSIP_C.UPDATE)
        {
          this._sendUpdate();
        }
        else
        {
          this._sendReinvite();
        }
      }, expires * 500); // Half the given interval (as the RFC states).
    }

    // I'm not the refresher.
    else
    {
      this._sessionTimers.timer = setTimeout(() =>
      {
        if (this._status === C.STATUS_TERMINATED) { return; }

        debugerror('runSessionTimer() | timer expired, terminating the session');

        this.terminate({
          cause         : JsSIP_C.causes.REQUEST_TIMEOUT,
          status_code   : 408,
          reason_phrase : 'Session Timer Expired'
        });
      }, expires * 1100);
    }
  }

  _newRTCSession(originator, request)
  {
    debug('newRTCSession()');

    this._ua.newRTCSession(this, {
      originator,
      session : this,
      request
    });
  }

  _connecting(request)
  {
    debug('session connecting');

    debug('emit "connecting"');

    this.emit('connecting', {
      request
    });
  }

  _progress(originator, response)
  {
    debug('session progress');

    debug('emit "progress"');

    this.emit('progress', {
      originator,
      response : response || null
    });
  }

  _accepted(originator, message)
  {
    debug('session accepted');

    this._start_time = new Date();

    debug('emit "accepted"');

    this.emit('accepted', {
      originator,
      response : message || null
    });
  }

  _confirmed(originator, ack)
  {
    debug('session confirmed');

    this._is_confirmed = true;

    debug('emit "confirmed"');

    this.emit('confirmed', {
      originator,
      ack : ack || null
    });
  }

  _ended(originator, message, cause)
  {
    debug('session ended');

    this._end_time = new Date();

    this._close();

    debug('emit "ended"');

    this.emit('ended', {
      originator,
      message : message || null,
      cause
    });
  }

  _failed(originator, message, cause)
  {
    debug('session failed');

    this._close();

    debug('emit "failed"');

    this.emit('failed', {
      originator,
      message : message || null,
      cause
    });
  }
};
