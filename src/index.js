import React from 'react'
import { render } from 'react-dom'
import { Typography } from './lib'

const App = () => (
  <div style={{ width: 640, margin: '15px auto' }}>
    <h1>Hello React</h1>
    <Typography.H1>Text</Typography.H1>
  </div>
)

render(<App />, document.getElementById('root'))
